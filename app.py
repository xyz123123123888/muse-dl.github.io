#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Muse AI 歌曲页下载器 (单文件 Flask 应用)
=====================================
用法:
    pip install -r requirements.txt
    python app.py
    浏览器打开 http://127.0.0.1:8765

功能:
    用户粘贴 h5.muse.top 链接 → 后端自动抓取歌曲元数据 (mp3 + 封面 + 简介)
    → 打包成 zip 供下载 → 默认在 downloads/ 目录保留 3 天,后台线程自动清理

抓取策略 (双层):
    1) requests 直调 project-api.atmob.com (快, 3~5 秒)
    2) 失败时回退 Playwright 真实打开页面抓 (慢, 15~30 秒, 鲁棒)
"""
from __future__ import annotations

import json
import logging
import os
import re
import threading
import time
import traceback
import uuid
import zipfile
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional
from urllib.parse import urlparse

import requests
from flask import Flask, jsonify, request, send_file

# ============== 可调参数 ==============
HOST = "0.0.0.0"     # 绑定到所有网卡 (避免 127.0.0.1 独占导致容器/虚拟网访问问题)
PORT = 48721         # 高位动态端口段, 基本不会被系统/常见软件占用
ROOT = Path(__file__).parent.resolve()
DOWNLOADS_DIR = ROOT / "downloads"          # zip 和临时任务目录都放这里
TASK_TMP_DIR = DOWNLOADS_DIR / "_tasks"     # 任务进行中的原始资源
KEEP_DAYS = 3                                # 文件保留天数
CLEANUP_INTERVAL_SEC = 3600                  # 清理线程扫描间隔
PLAYWRIGHT_TIMEOUT_MS = 120000
PLAYWRIGHT_WAIT_AFTER_LOAD_MS = 12000

# 任务调度
MAX_CONCURRENT_TASKS = 2                     # 同时最多 2 个抓取任务 (避免开 5 个 Chromium 内存爆)
DEDUPE_WINDOW_SEC = 30                       # 同 work_id 在 30s 内只接受 1 次抓取请求
TASK_TTL_AFTER_DONE_SEC = 300                # 完成后 5 分钟从内存表里移除 (zip 文件本身在磁盘上保留 3 天)

# 下载重试
HTTP_RETRY_TIMES = 3                         # 资源下载重试次数
HTTP_RETRY_BASE_BACKOFF = 1.5                # 指数退避基数 (秒)

# 反盗链 headers (muse.top API 需要 referer 是 h5.muse.top)
COMMON_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
    ),
    "Referer": "https://h5.muse.top/",
    "Origin": "https://h5.muse.top",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
}

# muse.top 内部 API 端点 (从 H5 页面 JS 拦截得到)
MUSE_SONG_INFO_URL = "https://project-api.atmob.com/project/song/v30/song/info"

# 触发 H5 页面 JS 发出 API 请求所需的 "客户端标识"
# (从抓包看到 — 平台似乎只校验 referer, 不严格校验 machineId)
MUSE_CLIENT_PAYLOAD = {
    "appPlatform": 3,
    "packageName": "com.xingchat.land.muse",
    "appVersionCode": "100",
    "appVersionName": "1.0.0",
}

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
log = logging.getLogger("muse-dl")

# ============== 内存任务表 ==============
# 本工具是单人本地使用, 状态全在内存里, 重启清空; zip 文件本身在磁盘上 3 天后自动删
tasks_lock = threading.Lock()
tasks: dict[str, "TaskState"] = {}
# 去重表: work_id -> task_id, 同 work_id 在进行中时新请求直接复用
recent_dedupe: dict[str, str] = {}
# 并发限流: 同时最多 MAX_CONCURRENT_TASKS 个抓取任务 (避免同时开多个 Chromium 内存爆)
task_semaphore = threading.BoundedSemaphore(MAX_CONCURRENT_TASKS)


@dataclass
class TaskState:
    task_id: str
    url: str
    work_id: str = ""
    status: str = "pending"          # pending | running | done | error
    stage: str = ""                  # 当前阶段文字 (给前端展示)
    progress: float = 0.0            # 0~1
    error: str = ""
    title: str = ""
    source: str = ""                 # requests | playwright
    file_id: str = ""                # 完成后 zip 的 file_id
    zip_filename: str = ""
    created_at: float = field(default_factory=time.time)
    finished_at: float = 0.0  # 任务结束时间戳 (0=未结束), 用于 TTL 清理


# ============== 工具函数 ==============
WORK_ID_RE = re.compile(r"[?&]id=([a-f0-9]{16,})", re.IGNORECASE)


def extract_work_id(url: str) -> str:
    """从 h5.muse.top 链接里抠出 workId (32 位 hex)。"""
    m = WORK_ID_RE.search(url)
    if not m:
        raise ValueError(f"无法从链接里识别 workId: {url}")
    return m.group(1)


def safe_filename(s: str, fallback: str = "untitled") -> str:
    """去掉路径里非法字符, 给 zip 里文件用。"""
    s = (s or "").strip()
    # Windows 禁字符 + 长度限制
    s = re.sub(r'[\\/:*?"<>|\r\n\t]', "_", s)
    s = re.sub(r"_+", "_", s).strip("._")
    return (s or fallback)[:80]


def guess_ext(url: str, content_type: str = "") -> str:
    """从 URL 路径或 Content-Type 猜后缀名。"""
    path = urlparse(url).path
    if "." in path.split("/")[-1]:
        ext = path.rsplit(".", 1)[-1].lower()
        if 2 <= len(ext) <= 5 and ext.isalnum():
            return "." + ext
    ct = content_type.lower().split(";")[0].strip()
    return {
        "audio/mpeg": ".mp3",
        "audio/mp3": ".mp3",
        "audio/mp4": ".m4a",
        "audio/x-m4a": ".m4a",
        "audio/flac": ".flac",
        "audio/x-flac": ".flac",
        "audio/ogg": ".ogg",
        "audio/wav": ".wav",
        "audio/x-wav": ".wav",
        "image/jpeg": ".jpg",
        "image/jpg": ".jpg",
        "image/png": ".png",
        "image/webp": ".webp",
        "image/gif": ".gif",
    }.get(ct, "")


# ============== 抓取: requests 主路 ==============
def fetch_via_requests(work_id: str) -> dict:
    """
    直接调 muse.top 的后端 API, 返回与 fetch_via_playwright 同 schema 的 dict。
    """
    payload = dict(MUSE_CLIENT_PAYLOAD, workId=work_id, machineId=uuid.uuid4().hex)
    r = requests.post(MUSE_SONG_INFO_URL, json=payload, headers=COMMON_HEADERS, timeout=20)
    r.raise_for_status()
    j = r.json()
    if j.get("code") != 0:
        raise RuntimeError(f"API 返回非成功: code={j.get('code')} msg={j.get('msg')}")
    data = j.get("data") or {}
    info = data.get("songInfo") or {}
    tpl = data.get("songTemplateInfo") or {}
    user = data.get("userInfo") or {}

    audio_url = info.get("audioUrl") or ""
    image_urls = []
    for k in ("imageUrl", "imageLargeUrl"):
        u = info.get(k)
        if u and u not in image_urls:
            image_urls.append(u)
    if not image_urls and tpl.get("imageUrl"):
        image_urls.append(tpl["imageUrl"])

    return {
        "work_id": work_id,
        "title": info.get("title") or tpl.get("title") or work_id,
        "duration": info.get("duration"),
        "audio_url": audio_url,
        "image_urls": image_urls,
        "lyrics": info.get("lyrics") or "",
        "introduction": info.get("introduction") or "",
        "user_name": user.get("userName") or user.get("nickname") or "",
        "extra": {"songInfo": info, "songTemplateInfo": tpl, "userInfo": user},
    }


# ============== 抓取: Playwright 备用 ==============
def fetch_via_playwright(url: str, work_id: str) -> dict:
    """
    真实启动 Chromium 打开 H5 页面, 监听 response 抓 mp3 + 图片, 并从 DOM 读 title。
    适用于: requests API 签名变更/被反爬时。
    """
    from playwright.sync_api import sync_playwright  # 懒加载, 没装也不影响主路

    audio_candidates: list[tuple[str, str]] = []  # (url, content_type)
    image_candidates: list[tuple[str, str]] = []

    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True)
        ctx = browser.new_context(
            user_agent=COMMON_HEADERS["User-Agent"],
            viewport={"width": 1280, "height": 800},
            locale="zh-CN",
        )
        page = ctx.new_page()

        def on_response(resp):
            try:
                ct = (resp.headers.get("content-type") or "").lower()
                u = resp.url
                if ct.startswith("audio/") or any(u.lower().endswith("." + e)
                        for e in ("mp3", "m4a", "aac", "flac", "ogg", "wav", "opus")):
                    audio_candidates.append((u, ct))
                elif ct.startswith("image/") or any(u.lower().endswith("." + e)
                        for e in ("jpg", "jpeg", "png", "webp", "gif", "bmp")):
                    image_candidates.append((u, ct))
            except Exception:
                pass

        page.on("response", on_response)
        page.goto(url, wait_until="load", timeout=PLAYWRIGHT_TIMEOUT_MS)
        page.wait_for_timeout(PLAYWRIGHT_WAIT_AFTER_LOAD_MS)

        # DOM 拿标题 + audio.src + 歌词(如果有)
        dom = page.evaluate("""
            () => {
                const audio = document.querySelector('audio');
                return {
                    title: document.title,
                    audioSrc: audio ? (audio.currentSrc || audio.src) : '',
                    bodyText: (document.body?.innerText || '').slice(0, 200),
                };
            }
        """)
        browser.close()

    # 合并 audio: 优先 <audio> 的 src (一定可播), 然后是抓到的
    audio_url = dom.get("audioSrc") or ""
    if not audio_url:
        # 兜底: 取第一个 Content-Type 为 audio/* 的响应
        for u, ct in audio_candidates:
            if ct.startswith("audio/"):
                audio_url = u
                break
        if not audio_url and audio_candidates:
            audio_url = audio_candidates[0][0]

    # 封面优先取大图 (尺寸 ≥ 200 像素的 jpeg/png/webp)
    image_urls = []
    seen = set()
    for u, ct in image_candidates:
        if u in seen:
            continue
        seen.add(u)
        if "icon" in u or "favicon" in u or "avatar" in u.lower():
            continue
        image_urls.append(u)
        if len(image_urls) >= 4:
            break

    return {
        "work_id": work_id,
        "title": dom.get("title") or work_id,
        "duration": None,
        "audio_url": audio_url,
        "image_urls": image_urls,
        "lyrics": "",
        "introduction": dom.get("bodyText", ""),
        "user_name": "",
        "extra": {"via": "playwright", "audio_candidates": audio_candidates,
                  "image_candidates": image_candidates},
    }


def fetch_metadata(url: str) -> tuple[dict, str]:
    """
    抓取入口: 先 requests, 失败回退 playwright。
    返回 (metadata_dict, source_str)。
    """
    work_id = extract_work_id(url)
    try:
        log.info("尝试 requests 直调 API: work_id=%s", work_id)
        meta = fetch_via_requests(work_id)
        log.info("requests 成功: title=%s audio=%s", meta["title"], meta["audio_url"][:80])
        return meta, "requests"
    except Exception as e:
        log.warning("requests 失败 (%s), 回退到 Playwright", e)
    try:
        meta = fetch_via_playwright(url, work_id)
        log.info("playwright 成功: title=%s audio=%s", meta["title"], meta["audio_url"][:80])
        return meta, "playwright"
    except Exception as e:
        raise RuntimeError(f"requests 和 playwright 两条路都失败: {e}") from e


# ============== 下载 + 打包 ==============
def _http_download(url: str, dst: Path, referer: str = "https://h5.muse.top/") -> int:
    """
    流式下载, 边下边写文件。失败指数退避重试最多 HTTP_RETRY_TIMES 次。
    返回字节数。
    """
    import time as _t
    headers = dict(COMMON_HEADERS, Referer=referer)
    last_err: Exception | None = None
    for attempt in range(1, HTTP_RETRY_TIMES + 1):
        try:
            with requests.get(url, headers=headers, stream=True, timeout=60) as r:
                r.raise_for_status()
                dst.parent.mkdir(parents=True, exist_ok=True)
                total = 0
                with open(dst, "wb") as f:
                    for chunk in r.iter_content(chunk_size=64 * 1024):
                        if chunk:
                            f.write(chunk)
                            total += len(chunk)
                return total
        except Exception as e:
            last_err = e
            log.warning("下载失败 (尝试 %d/%d) %s: %s", attempt, HTTP_RETRY_TIMES, url[:80], e)
            if attempt < HTTP_RETRY_TIMES:
                _t.sleep(HTTP_RETRY_BASE_BACKOFF ** attempt)
    # 全部失败, 清理半成品
    try:
        if dst.exists():
            dst.unlink()
    except Exception:
        pass
    raise RuntimeError(f"下载失败 {url[:80]}: {last_err}")


def build_zip(task_dir: Path, meta: dict, file_id: str, on_progress=None) -> tuple[Path, str]:
    """
    把所有资源下载到 task_dir, 打成 zip, 存到 DOWNLOADS_DIR。
    返回 (zip_path, zip_name)。
    失败时自动清理 task_dir 和已生成的 zip 半成品。
    """
    task_dir.mkdir(parents=True, exist_ok=True)
    title_safe = safe_filename(meta.get("title") or meta["work_id"])
    audio_url = meta.get("audio_url") or ""
    image_urls = meta.get("image_urls") or []

    def _cleanup() -> None:
        """失败/异常时清理 task_dir, 防止残留垃圾文件。"""
        try:
            if task_dir.exists():
                for f in task_dir.iterdir():
                    try:
                        if f.is_file():
                            f.unlink()
                        elif f.is_dir():
                            import shutil
                            shutil.rmtree(f, ignore_errors=True)
                    except Exception:
                        pass
                try:
                    task_dir.rmdir()
                except Exception:
                    pass
        except Exception:
            pass

    try:
        # 计算子任务权重, 让进度条平滑过渡 (0.45 ~ 0.95)
        n_images_to_try = min(len(image_urls), 4)
        sub_total = 1 + n_images_to_try  # 1 音乐 + N 图片
        sub_idx = 0

        # 1) 音乐
        audio_path: Optional[Path] = None
        if not audio_url:
            raise RuntimeError("没有 audio_url, 无法下载音乐")
        ext = guess_ext(audio_url, "") or ".mp3"
        audio_path = task_dir / f"song{ext}"
        sub_idx += 1
        if on_progress:
            on_progress(f"下载音乐 {audio_path.name}", 0.45 + 0.45 * (sub_idx / sub_total))
        n = _http_download(audio_url, audio_path)
        log.info("音频下载完成: %s (%d bytes)", audio_path, n)

        # 2) 封面图
        image_paths: list[Path] = []
        for i, img_url in enumerate(image_urls[:4], 1):
            ext = guess_ext(img_url, "") or ".jpg"
            img_path = task_dir / f"cover_{i}{ext}"
            sub_idx += 1
            if on_progress:
                on_progress(f"下载图片 {i}/{n_images_to_try}", 0.45 + 0.45 * (sub_idx / sub_total))
            try:
                _http_download(img_url, img_path)
                image_paths.append(img_path)
            except Exception as e:
                log.warning("图片下载失败 (继续) %s: %s", img_url[:80], e)

        # 3) 歌词 (如果有非空 lyrics)
        lyrics_path: Optional[Path] = None
        lyrics_text = (meta.get("lyrics") or "").strip()
        if lyrics_text:
            # 简单存成 .lrc 格式 (没时间轴也是合法 lrc)
            lyrics_path = task_dir / "lyrics.lrc"
            header = f"[ti:{meta.get('title','')}]\n[ar:{meta.get('user_name','')}]\n"
            lyrics_path.write_text(header + lyrics_text, encoding="utf-8")

        # 4) info.json
        info_path = task_dir / "info.json"
        info_path.write_text(
            json.dumps({
                "work_id": meta.get("work_id"),
                "title": meta.get("title"),
                "user_name": meta.get("user_name"),
                "duration_sec": meta.get("duration"),
                "introduction": meta.get("introduction"),
                "audio_url": audio_url,
                "image_urls": image_urls,
                "source": meta.get("source", ""),
                "fetched_at": datetime.now().isoformat(timespec="seconds"),
                "extra": meta.get("extra", {}),
            }, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

        # 5) 打包 zip — file_id 由调用方提前生成并传入,避免完成后才赋值导致的轮询间隙 Bug
        if on_progress:
            on_progress("打包 zip", 0.95)
        zip_name = f"muse_{meta['work_id'][:8]}_{file_id}.zip"
        zip_path = DOWNLOADS_DIR / zip_name
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            # 主要文件用歌名命名
            arc_audio = f"{title_safe}{audio_path.suffix}"
            zf.write(audio_path, arcname=arc_audio)
            # 封面图
            for i, ip in enumerate(image_paths, 1):
                zf.write(ip, arcname=f"cover_{i}{ip.suffix}")
            # 歌词
            if lyrics_path:
                zf.write(lyrics_path, arcname=f"{title_safe}.lrc")
            # 元数据始终放在根
            zf.write(info_path, arcname="info.json")
            # README
            readme = (
                f"标题: {meta.get('title','')}\n"
                f"作者: {meta.get('user_name','')}\n"
                f"时长: {meta.get('duration','')} 秒\n"
                f"workId: {meta.get('work_id','')}\n"
                f"简介: {meta.get('introduction','')}\n"
                f"抓取来源: {meta.get('source','')}\n"
                f"抓取时间: {datetime.now().isoformat(timespec='seconds')}\n"
            )
            zf.writestr("README.txt", readme)

        # 任务目录删掉原始文件 (zip 已包含), 省空间
        _cleanup()

        return zip_path, zip_name

    except Exception:
        # 任何环节失败: 清理 task_dir 和可能已经创建的半成品 zip
        _cleanup()
        # 尝试删可能存在的半成品 zip
        try:
            half_zip = DOWNLOADS_DIR / f"muse_{meta['work_id'][:8]}_{file_id}.zip"
            if half_zip.exists():
                half_zip.unlink()
        except Exception:
            pass
        raise


# ============== 任务执行 ==============
def run_task(task_id: str, url: str) -> None:
    """后台线程入口: 抓取 → 打包 → 更新状态。用 Semaphore 限制并发数。"""
    with tasks_lock:
        t = tasks[task_id]
        t.status = "running"
        t.stage = "等待抓取资源"

    def set_stage(text: str, progress: Optional[float] = None) -> None:
        with tasks_lock:
            t.stage = text
            if progress is not None:
                t.progress = progress
        log.info("[%s] %s", task_id, text)

    # 等到拿到信号量 (最多等 10 分钟, 超过直接放弃)
    if not task_semaphore.acquire(timeout=600):
        with tasks_lock:
            t.status = "error"
            t.error = "服务繁忙, 等待资源超时"
            t.stage = "服务繁忙"
            t.finished_at = time.time()
        log.warning("[%s] 资源等待超时", task_id)
        return

    try:
        set_stage("解析链接", 0.05)
        work_id = extract_work_id(url)
        with tasks_lock:
            t.work_id = work_id

        # ---- 抓取元数据 (requests → playwright) ----
        set_stage("抓取歌曲信息", 0.15)
        meta, source = fetch_metadata(url)
        with tasks_lock:
            t.title = meta["title"]
            t.source = source

        meta["source"] = source  # 传给 build_zip
        set_stage(f"抓取完成 (via {source})", 0.45)

        # ---- 下载 + 打包 ----
        # file_id 必须在这里生成,在 build_zip 返回前就赋值给 t.file_id,
        # 消除"status=done 但 file_id 还未赋值"的轮询间隙 Bug。
        # 内部用短 uuid (build_zip 拼成 muse_{work_id[:8]}_{file_id}.zip),
        # 完成后覆盖为 zip 完整 stem, 让 /download/{file_id} 路由直接 .zip 拼接能匹配。
        file_id = uuid.uuid4().hex[:16]
        task_dir = TASK_TMP_DIR / task_id
        with tasks_lock:
            t.file_id = file_id
        zip_path, zip_name = build_zip(
            task_dir, meta, file_id,
            on_progress=lambda text, p: set_stage(text, p),
        )
        with tasks_lock:
            t.zip_filename = zip_name
            t.file_id = zip_name.rsplit(".", 1)[0]  # 完整 stem, 跟 history 接口和 download 路由对齐
            t.status = "done"
            t.finished_at = time.time()
        set_stage("打包完成", 1.0)
        log.info("[%s] 任务完成, zip=%s", task_id, zip_name)

    except Exception as e:
        log.error("[%s] 任务失败: %s\n%s", task_id, e, traceback.format_exc())
        with tasks_lock:
            t.status = "error"
            t.error = str(e)
            t.stage = "失败"
            t.finished_at = time.time()
    finally:
        task_semaphore.release()


def cleanup_finished_tasks() -> int:
    """清理内存里已结束超过 TASK_TTL_AFTER_DONE_SEC 的任务 (zip 文件在磁盘上保留更久)。"""
    now = time.time()
    removed = 0
    with tasks_lock:
        to_remove = [
            tid for tid, t in tasks.items()
            if t.finished_at > 0 and (now - t.finished_at) > TASK_TTL_AFTER_DONE_SEC
        ]
        for tid in to_remove:
            tasks.pop(tid, None)
            removed += 1
    if removed:
        log.info("清理已结束任务: 从内存表删除 %d 个", removed)
    return removed


def cleanup_recent_dedupe() -> None:
    """清理 recent_dedupe 里过期的 work_id (DEDUPE_WINDOW_SEC 之外)。"""
    # 由于没存时间戳, 用"对应 task 不在 tasks 里"作为过期的标志
    with tasks_lock:
        stale = [wid for wid, tid in recent_dedupe.items() if tid not in tasks]
        for wid in stale:
            recent_dedupe.pop(wid, None)


# ============== 清理线程 ==============
def cleanup_expired() -> int:
    """删除 downloads/ 下 mtime 超过 KEEP_DAYS 的 zip 和空目录。返回删除数。"""
    if not DOWNLOADS_DIR.exists():
        return 0
    cutoff = time.time() - KEEP_DAYS * 86400
    deleted = 0
    for p in DOWNLOADS_DIR.iterdir():
        try:
            if p.is_file() and p.stat().st_mtime < cutoff:
                p.unlink()
                deleted += 1
            elif p.is_dir() and p != TASK_TMP_DIR:
                # 清理空的过期子目录
                if not any(p.iterdir()) and p.stat().st_mtime < cutoff:
                    p.rmdir()
                    deleted += 1
        except Exception:
            pass
    # 任务临时目录里残留的也清掉
    if TASK_TMP_DIR.exists():
        for p in TASK_TMP_DIR.iterdir():
            try:
                if p.is_dir() and not any(p.iterdir()) and p.stat().st_mtime < cutoff:
                    p.rmdir()
                elif p.is_file() and p.stat().st_mtime < cutoff:
                    p.unlink()
            except Exception:
                pass
    if deleted:
        log.info("清理过期文件: 删除 %d 个", deleted)
    return deleted


def cleanup_loop() -> None:
    """后台线程: 每小时扫一次。"""
    while True:
        try:
            cleanup_expired()         # 磁盘 zip 过期清理
            cleanup_finished_tasks()  # 内存任务表清理
            cleanup_recent_dedupe()   # 去重表清理
        except Exception as e:
            log.warning("清理异常: %s", e)
        time.sleep(CLEANUP_INTERVAL_SEC)


# ============== Flask 应用 ==============
app = Flask(__name__)


@app.route("/")
def index():
    # 直接返回 HTML 字符串, 不用 render_template_string (避免 Jinja2 把 JS 里的 {} 当成模板语法)
    return INDEX_HTML


@app.route("/api/fetch", methods=["POST"])
def api_fetch():
    data = request.get_json(silent=True) or {}
    url = (data.get("url") or "").strip()
    if not url:
        return jsonify({"ok": False, "error": "缺少 url"}), 400
    if "h5.muse.top" not in url:
        return jsonify({"ok": False, "error": "只支持 h5.muse.top 链接"}), 400
    try:
        work_id = extract_work_id(url)  # 立刻校验, 链接不对直接 400
    except ValueError as e:
        return jsonify({"ok": False, "error": str(e)}), 400

    # 去重: 同 work_id 短时间内已存在任务, 直接返回现有 task_id (不重新跑)
    with tasks_lock:
        existing_tid = recent_dedupe.get(work_id)
        if existing_tid and existing_tid in tasks:
            t = tasks[existing_tid]
            # 只对还在进行中的任务去重; 已完成的让用户重新下载即可 (zip 在磁盘上)
            if t.status in ("pending", "running"):
                return jsonify({
                    "ok": True, "task_id": existing_tid, "deduped": True,
                    "stage": t.stage, "progress": t.progress,
                })

        # 清理 recent_dedupe 里的过期项 (找不到对应任务)
        stale = [wid for wid, tid in recent_dedupe.items() if tid not in tasks]
        for wid in stale:
            recent_dedupe.pop(wid, None)

    task_id = uuid.uuid4().hex[:12]
    with tasks_lock:
        tasks[task_id] = TaskState(task_id=task_id, url=url, work_id=work_id)
        recent_dedupe[work_id] = task_id
    threading.Thread(target=run_task, args=(task_id, url), daemon=True).start()
    return jsonify({"ok": True, "task_id": task_id, "deduped": False})


@app.route("/api/history", methods=["GET"])
def api_history():
    """返回磁盘上已存在的 zip 历史列表 (按 mtime 倒序, 最多 50 条)。"""
    if not DOWNLOADS_DIR.exists():
        return jsonify({"ok": True, "items": []})
    items = []
    for p in DOWNLOADS_DIR.iterdir():
        if not p.is_file() or p.suffix != ".zip":
            continue
        try:
            st = p.stat()
        except Exception:
            continue
        # 跳过非 muse 前缀的 zip (如用户手动放进来的)
        if not p.name.startswith("muse_"):
            continue
        items.append({
            "file_id": p.stem,
            "filename": p.name,
            "size": st.st_size,
            "mtime": int(st.st_mtime),
        })
    items.sort(key=lambda x: x["mtime"], reverse=True)
    items = items[:50]
    return jsonify({"ok": True, "items": items})


@app.route("/api/status/<task_id>")
def api_status(task_id: str):
    with tasks_lock:
        t = tasks.get(task_id)
    if not t:
        return jsonify({"ok": False, "error": "任务不存在"}), 404
    return jsonify({
        "ok": True,
        "task_id": t.task_id,
        "status": t.status,
        "stage": t.stage,
        "progress": t.progress,
        "title": t.title,
        "source": t.source,
        "work_id": t.work_id,
        "error": t.error,
        "file_id": t.file_id,
        "zip_filename": t.zip_filename,
    })


@app.route("/download/<file_id>")
def download(file_id: str):
    """根据 file_id (即 zip 文件名去掉 .zip) 给出 zip。"""
    # 防 path traversal: 只允许 [A-Za-z0-9_-]
    if not re.fullmatch(r"[A-Za-z0-9_\-]+", file_id):
        return jsonify({"ok": False, "error": "非法 file_id"}), 400
    zip_path = DOWNLOADS_DIR / f"{file_id}.zip"
    if not zip_path.exists():
        return jsonify({"ok": False, "error": "文件不存在或已被清理"}), 404
    # 顺手更新一下 mtime (用户重新下载时刷新 3 天倒计时)
    try:
        os.utime(zip_path, None)
    except Exception:
        pass
    return send_file(
        zip_path,
        as_attachment=True,
        download_name=zip_path.name,
        mimetype="application/zip",
    )


# ============== HTML 模板 (内嵌) ==============
INDEX_HTML = r"""<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>muse-dl</title>
<style>
  /* ============================================
     muse-dl :: 终端复古主题
     配色: 磷光绿 phosphor green on near-black
     字体: 等宽 monospace
     效果: CRT 扫描线 + 边缘暗角 + 文字微发光
     ============================================ */

  :root {
    --bg:        #0a0a0a;
    --bg-panel:  #050505;
    --fg:        #00ff41;       /* phosphor green */
    --fg-dim:    #00b830;
    --fg-mute:   #4a6a4a;       /* 极淡绿, 注释/未激活 */
    --err:       #ff5555;
    --warn:      #ffaa00;       /* amber, 用于 alert 弹窗标题 */
    --text-dim:  #6a6a6a;       /* 底部 footer 灰字 */
    --border:    #1a3a1a;
  }

  * { box-sizing: border-box; }

  html, body { margin: 0; padding: 0; }

  body {
    font-family: ui-monospace, "Cascadia Code", "JetBrains Mono", "Fira Code",
                 "SF Mono", Consolas, "Courier New", monospace;
    font-size: 14px;
    line-height: 1.55;
    color: var(--fg);
    background: var(--bg);
    min-height: 100vh;
    padding: 28px 18px 18px;
    /* 文字轻微磷光 */
    text-shadow: 0 0 2px rgba(0, 255, 65, 0.35);
  }

  /* CRT 扫描线 (横纹) :: 覆盖在内容之上, 不接收事件 */
  body::before {
    content: "";
    position: fixed; inset: 0;
    pointer-events: none;
    z-index: 9000;
    background: repeating-linear-gradient(
      0deg,
      rgba(0, 0, 0, 0)   0px,
      rgba(0, 0, 0, 0)   2px,
      rgba(0, 255, 65, 0.05) 2px,
      rgba(0, 255, 65, 0.05) 3px
    );
  }
  /* CRT 边缘暗角 ::after */
  body::after {
    content: "";
    position: fixed; inset: 0;
    pointer-events: none;
    z-index: 9001;
    background: radial-gradient(
      ellipse at center,
      transparent 55%,
      rgba(0, 0, 0, 0.55) 100%
    );
  }

  /* ---- 顶部 ASCII 标题 ---- */
  .ascii {
    white-space: pre;
    color: var(--fg);
    text-shadow: 0 0 6px rgba(0, 255, 65, 0.6);
    font-size: 13px;
    line-height: 1.1;
    margin: 0 0 6px;
    user-select: none;
  }
  /* 终端打印光标 ▌ */
  .cursor {
    display: inline-block;
    width: 0.55em;
    background: var(--fg);
    box-shadow: 0 0 6px var(--fg);
    animation: blink 1s steps(1) infinite;
    vertical-align: text-bottom;
    margin-left: 2px;
  }
  @keyframes blink { 50% { opacity: 0; } }

  /* 顶部状态条 (登录 banner 风格) */
  .banner {
    color: var(--fg-dim);
    font-size: 12px;
    margin: 8px 0 22px;
    padding-bottom: 10px;
    border-bottom: 1px dashed var(--border);
  }
  .banner .dot { color: var(--fg-mute); margin: 0 8px; }

  /* ---- 主面板: 一个无圆角的"终端窗口" ---- */
  .term {
    max-width: 760px;
    margin: 0 auto;
    border: 1px solid var(--fg-dim);
    background: var(--bg-panel);
    padding: 18px 20px 22px;
    /* 屏内阴影: 模拟老 CRT 的凹陷 */
    box-shadow:
      inset 0 0 40px rgba(0, 255, 65, 0.04),
      0 0 0 1px rgba(0, 255, 65, 0.05);
  }

  .prompt-line {
    color: var(--fg-dim);
    margin-bottom: 6px;
    font-size: 13px;
  }
  .prompt-line .ps { color: var(--fg); }

  /* ---- 输入框 + 按钮 (终端 prompt 风格) ---- */
  .row {
    display: flex;
    gap: 8px;
    align-items: stretch;
    margin-bottom: 14px;
  }
  .row .ps-pre { color: var(--fg); align-self: center; padding-right: 4px; }
  input[type=text] {
    flex: 1;
    padding: 8px 10px;
    background: #000;
    color: var(--fg);
    border: 1px solid var(--fg-dim);
    border-radius: 0;
    font: inherit;
    font-size: 13px;
    outline: none;
    text-shadow: 0 0 2px rgba(0, 255, 65, 0.35);
  }
  input[type=text]:focus {
    border-color: var(--fg);
    box-shadow: 0 0 8px rgba(0, 255, 65, 0.4);
  }
  input[type=text]::placeholder { color: var(--fg-mute); }

  button {
    font: inherit;
    font-size: 13px;
    padding: 8px 16px;
    background: var(--fg);
    color: #000;
    border: 1px solid var(--fg);
    border-radius: 0;
    cursor: pointer;
    font-weight: 600;
    letter-spacing: 0.5px;
    text-shadow: none;
  }
  button:hover:not(:disabled) { background: #000; color: var(--fg); }
  button:disabled { background: var(--fg-mute); border-color: var(--fg-mute); color: #000; cursor: not-allowed; }

  /* ---- 字符进度条 ---- */
  .progress { margin: 12px 0 4px; }
  .bar-chars {
    font-size: 14px;
    letter-spacing: 0;
    color: var(--fg);
    text-shadow: 0 0 4px rgba(0, 255, 65, 0.6);
    white-space: pre;
  }
  .bar-chars .done { color: var(--fg); }
  .bar-chars .todo { color: var(--fg-mute); }
  .stage {
    color: var(--fg-dim);
    font-size: 12px;
    margin-top: 4px;
  }
  .stage::before { content: "> "; color: var(--fg); }

  /* ---- 结果区 (终端输出风格) ---- */
  .result {
    margin-top: 16px;
    padding: 12px 14px;
    border-left: 3px solid var(--fg-dim);
    background: rgba(0, 255, 65, 0.03);
    font-size: 13px;
  }
  .result.ok  { border-left-color: var(--fg);  }
  .result.err { border-left-color: var(--err); color: var(--err); text-shadow: 0 0 3px rgba(255,85,85,0.5); }
  .result .tag {
    display: inline-block;
    padding: 0 6px;
    margin-right: 6px;
    font-weight: 700;
    font-size: 12px;
  }
  .result.ok  .tag { background: var(--fg); color: #000; text-shadow: none; }
  .result.err .tag { background: var(--err); color: #000; text-shadow: none; }
  .result .line { margin: 2px 0; }
  .result .line .k { color: var(--fg-mute); display: inline-block; min-width: 80px; }
  .dl-btn {
    display: inline-block;
    margin-top: 8px;
    padding: 4px 10px;
    background: transparent;
    color: var(--fg);
    border: 1px solid var(--fg);
    text-decoration: none;
    font-weight: 600;
    text-shadow: 0 0 3px rgba(0, 255, 65, 0.5);
  }
  .dl-btn:hover { background: var(--fg); color: #000; text-shadow: none; }
  .dl-btn::before { content: "[ "; }
  .dl-btn::after  { content: " ]"; }

  /* ---- 历史下载 (ls -t 风格) ---- */
  .history {
    margin-top: 20px;
    padding-top: 14px;
    border-top: 1px dashed var(--border);
  }
  .history h3 {
    color: var(--fg-dim);
    font-size: 12px;
    font-weight: 400;
    margin: 0 0 8px;
  }
  .history h3::before { content: "# "; color: var(--fg-mute); }
  .history ul {
    list-style: none; padding: 0; margin: 0;
    max-height: 180px; overflow-y: auto;
    font-size: 12px;
  }
  .history li {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding: 2px 4px;
    color: var(--fg-dim);
  }
  .history li:hover { background: rgba(0, 255, 65, 0.05); }
  .history li .name { color: var(--fg); }
  .history li .meta { color: var(--fg-mute); margin: 0 8px; }
  .history li a {
    color: var(--fg);
    text-decoration: none;
    padding: 1px 6px;
    border: 1px solid var(--fg-dim);
  }
  .history li a:hover { background: var(--fg); color: #000; text-shadow: none; }
  .history-empty { color: var(--fg-mute); font-style: italic; font-size: 12px; }

  /* ---- 页面底部 footer ---- */
  .footer {
    max-width: 760px;
    margin: 14px auto 0;
    text-align: center;
    color: var(--text-dim);
    font-size: 11px;
    text-shadow: none;
  }
  .footer::before { content: "# "; color: var(--fg-mute); }

  /* ---- 免责协议弹窗 (终端 ALERT 风格) ---- */
  .modal-overlay {
    position: fixed; inset: 0;
    background: rgba(0, 0, 0, 0.78);
    display: flex; align-items: center; justify-content: center;
    z-index: 9999;
    padding: 16px;
  }
  .modal {
    background: var(--bg-panel);
    border: 1px solid var(--warn);
    color: var(--fg);
    max-width: 560px;
    width: 100%;
    padding: 0;
    font: inherit;
    box-shadow:
      0 0 0 1px rgba(255, 170, 0, 0.2),
      0 0 30px rgba(255, 170, 0, 0.15),
      inset 0 0 40px rgba(255, 170, 0, 0.04);
  }
  .modal-header {
    background: var(--warn);
    color: #000;
    padding: 6px 14px;
    font-weight: 700;
    font-size: 13px;
    letter-spacing: 0.5px;
    text-shadow: none;
  }
  .modal-body { padding: 16px 20px 6px; font-size: 13px; }
  .modal-body p { margin: 0 0 10px; color: var(--warn); font-weight: 600; }
  .modal-body ul {
    list-style: none; padding: 0; margin: 0 0 12px;
    color: var(--fg-dim); line-height: 1.7;
  }
  .modal-body ul li::before { content: "* "; color: var(--fg-mute); }
  .check-row {
    display: flex; align-items: flex-start; gap: 8px;
    margin: 12px 0 0;
    cursor: pointer; user-select: none;
    color: var(--fg);
  }
  .check-row input { margin-top: 4px; accent-color: var(--fg); transform: scale(1.1); }
  .modal-actions {
    display: flex; gap: 10px; justify-content: flex-end;
    padding: 14px 20px 18px;
  }
  .modal button {
    padding: 6px 16px;
    font-size: 12px;
    font-weight: 700;
    border-radius: 0;
  }
  .modal .btn-cancel {
    background: transparent;
    color: var(--fg-mute);
    border: 1px solid var(--fg-mute);
  }
  .modal .btn-cancel:hover { background: var(--fg-mute); color: #000; text-shadow: none; }
  .modal .btn-accept { background: var(--fg); color: #000; border: 1px solid var(--fg); }
  .modal .btn-accept:hover { background: #000; color: var(--fg); }
  .modal .btn-accept:disabled {
    background: transparent; color: var(--fg-mute);
    border: 1px dashed var(--fg-mute); cursor: not-allowed;
  }
  .modal .btn-accept:disabled:hover { background: transparent; color: var(--fg-mute); }
</style>
</head>
<body>
<!-- 免责协议弹窗: 首次或 3 分钟过期后弹出, 必须勾选同意后关闭 -->
<div class="modal-overlay" id="modalOverlay">
  <div class="modal">
    <div class="modal-header">[!] ALERT :: USE FOR LEARNING & TECHNICAL STUDY ONLY</div>
    <div class="modal-body">
      <p>本工具仅供学习与技术交流使用, 严禁用于任何非法用途。</p>
      <ul>
        <li>本项目仅用于<strong>学习技术原理</strong>, 不提供任何形式的打包发布服务。</li>
        <li>所有从第三方平台下载的内容, 其版权归原作者或平台所有, 请自行遵守平台的使用条款与相关法律法规。</li>
        <li>您不得将下载的文件用于商业传播、二次分发、二次创作牟利、侵犯他人权益等任何非法或不当用途。</li>
        <li>使用本工具造成的一切后果由使用者本人承担, 项目作者不承担任何法律责任。</li>
        <li>如您所在地区的法律法规不允许此类操作, 请立即停止使用并关闭本页面。</li>
      </ul>
      <label class="check-row">
        <input type="checkbox" id="agreeCheck" onchange="onAgreeChange()" onclick="onAgreeChange()">
        <span>我已完整阅读并同意以上条款, 承诺仅将本工具用于合法的学习交流用途。</span>
      </label>
    </div>
    <div class="modal-actions">
      <button class="btn-cancel" id="rejectBtn" type="button" onclick="onReject()">[ REJECT ]</button>
      <button class="btn-accept" id="acceptBtn" type="button" disabled onclick="onAccept()">[ ACCEPT ]</button>
    </div>
  </div>
</div>

<div class="term">
<pre class="ascii"> __  __ _____ ____  _      ____
|  \/  |  _  / ___|| |    |  _ \
| |\/| | |_| \___ \| |    | | | |
|_|  |_|_____/___ /| |___ |_| |_|
                                        <span class="cursor"></span></pre>

  <div class="banner">
    <span>muse-dl v0.1.0</span><span class="dot">::</span>
    <span>h5.muse.top song scraper</span><span class="dot">::</span>
    <span>keep 72h</span><span class="dot">::</span>
    <span>2 concurrent</span>
  </div>

  <div class="prompt-line"><span class="ps">$</span> paste h5.muse.top link and press ENTER:</div>
  <div class="row">
    <span class="ps-pre">&gt;</span>
    <input type="text" id="urlInput" autocomplete="off" spellcheck="false"
           placeholder="https://h5.muse.top/song?id=...">
    <button id="goBtn">[ DOWNLOAD ]</button>
  </div>

  <div class="progress" id="progressBox" style="display:none">
    <div class="bar-chars" id="barChars">[                    ]   0%</div>
    <div class="stage" id="stageText">idle</div>
  </div>

  <div class="result" id="resultBox" style="display:none"></div>

  <div class="history" id="historyBox" style="display:none">
    <h3>history (ls -t downloads/ -- newest first, max 50)</h3>
    <ul id="historyList"></ul>
  </div>
</div>

<div class="footer">仅供学习交流使用, 严禁用于非法用途</div>

<script>
// ===== 免责协议 =====
window.syncAcceptBtn = function() {
  const a = document.getElementById('acceptBtn');
  const c = document.getElementById('agreeCheck');
  if (!a || !c) return;
  a.disabled = !c.checked;
};

window.closeModal = function() {
  const o = document.getElementById('modalOverlay');
  if (o) o.style.display = 'none';
  try { sessionStorage.setItem('muse_dl_disclaimer_shown', String(Date.now())); } catch (_) {}
  window.dispatchEvent(new Event('__disclaimer_closed'));
};

window.onAgreeChange = function() { window.syncAcceptBtn(); };

window.onAccept = function() {
  const c = document.getElementById('agreeCheck');
  if (!c || !c.checked) { window.syncAcceptBtn(); return; }
  window.closeModal();
};

window.onReject = function() {
  if (!confirm('您必须同意协议后才能使用本工具, 确定要离开吗?')) return;
  if (Math.random() < 0.5) {
    // rickroll 概率分支
    const win = window.open('', '_self');
    win.document.write(
      '<!doctype html><html><head><meta charset="utf-8">' +
      '<title>redirecting...</title>' +
      '<style>body{margin:0;background:#000;color:#00ff41;font-family:ui-monospace,Consolas,monospace;display:flex;align-items:center;justify-content:center;height:100vh;text-align:center;}' +
      'h1{font-size:42px;margin:0 0 16px;letter-spacing:2px;text-shadow:0 0 8px #00ff41;animation:shake .3s infinite alternate;}' +
      '@keyframes shake{from{transform:translate(-2px,0);}to{transform:translate(2px,0);}}' +
      'p{color:#00b830;}</style></head>' +
      '<body><div><h1>&gt;_  you got rickrolled</h1>' +
      '<p>redirecting to bilibili in 3s ...</p>' +
      '<script>setTimeout(function(){location.replace("https://www.bilibili.com/video/BV1hq4y1s7VH");}, 3000);<\/script>' +
      '</div></body></html>'
    );
    win.document.close();
  } else {
    document.body.innerHTML =
      '<div style="display:flex;align-items:center;justify-content:center;height:100vh;background:#0a0a0a;color:#6a6a6a;font-family:ui-monospace,Consolas,monospace;">&gt; access denied. please close this page.</div>';
  }
};

window.__initDisclaimer = function() {
  let skip = false;
  try {
    const shown = parseInt(sessionStorage.getItem('muse_dl_disclaimer_shown') || "0", 10);
    if (shown && (Date.now() - shown) < 3 * 60 * 1000) skip = true;
  } catch (_) {}
  const o = document.getElementById('modalOverlay');
  if (skip) {
    if (o) o.style.display = 'none';
    window.__disclaimer_skipped = true;
    window.dispatchEvent(new Event('__disclaimer_closed'));
  }
};
window.__initDisclaimer();

// ===== 业务 =====
const $ = (id) => document.getElementById(id);
const urlInput = $('urlInput');
const goBtn = $('goBtn');
const progressBox = $('progressBox');
const barChars = $('barChars');
const stageText = $('stageText');
const resultBox = $('resultBox');
const historyBox = $('historyBox');
const historyList = $('historyList');

let pollTimer = null;

const BAR_WIDTH = 20;
function renderBar(p) {
  const n = Math.max(0, Math.min(1, p || 0));
  const done = Math.round(n * BAR_WIDTH);
  const todo = BAR_WIDTH - done;
  const pct = Math.round(n * 100) + '%';
  return '[' + '#'.repeat(done) + '-'.repeat(todo) + '] ' + pct.padStart(3, ' ');
}

function showResult(kind, html) {
  resultBox.className = 'result ' + kind;
  resultBox.innerHTML = html;
  resultBox.style.display = 'block';
}
function reset() {
  progressBox.style.display = 'none';
  resultBox.style.display = 'none';
  barChars.textContent = renderBar(0);
  stageText.textContent = 'idle';
}
function fmtSize(n) {
  if (n < 1024) return n + 'B';
  if (n < 1024*1024) return (n/1024).toFixed(1) + 'K';
  if (n < 1024*1024*1024) return (n/1024/1024).toFixed(1) + 'M';
  return (n/1024/1024/1024).toFixed(2) + 'G';
}
function fmtTimeAgo(ts) {
  const sec = Math.max(0, Math.floor(Date.now()/1000 - ts));
  if (sec < 60)    return sec + 's ago';
  if (sec < 3600)  return Math.floor(sec/60) + 'm ago';
  if (sec < 86400) return Math.floor(sec/3600) + 'h ago';
  return Math.floor(sec/86400) + 'd ago';
}
function escapeHtml(s) {
  return (s || '').replace(/[&<>"']/g, c =>
    ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}

async function loadHistory() {
  try {
    const r = await fetch('/api/history');
    const j = await r.json();
    if (!j.ok || !j.items || j.items.length === 0) {
      historyList.innerHTML = '<li class="history-empty">// (empty)</li>';
      historyBox.style.display = 'block';
      return;
    }
    historyList.innerHTML = j.items.map(it =>
      '<li>' +
        '<span><span class="name">' + it.filename + '</span>' +
        ' <span class="meta">' + fmtSize(it.size) + '  ' + fmtTimeAgo(it.mtime) + '</span></span>' +
        '<a href="/download/' + it.file_id + '">dl</a>' +
      '</li>'
    ).join('');
    historyBox.style.display = 'block';
  } catch (_) {}
}

async function start() {
  const url = urlInput.value.trim();
  if (!url) { stageText.textContent = '> error: empty input'; return; }
  reset();
  goBtn.disabled = true;
  goBtn.textContent = '[ ... ]';
  try {
    const r = await fetch('/api/fetch', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({url}),
    });
    const j = await r.json();
    if (!j.ok) {
      showResult('err', '<span class="tag">[ERR]</span>' + escapeHtml(j.error));
      goBtn.disabled = false;
      goBtn.textContent = '[ DOWNLOAD ]';
      return;
    }
    if (j.deduped) {
      stageText.textContent = 'dedup hit, sharing existing task: ' + (j.stage || '');
    }
    progressBox.style.display = 'block';
    if (pollTimer) clearInterval(pollTimer);
    pollTimer = setInterval(() => pollStatus(j.task_id), 800);
  } catch (e) {
    showResult('err', '<span class="tag">[ERR]</span>network: ' + e.message);
    goBtn.disabled = false;
    goBtn.textContent = '[ DOWNLOAD ]';
  }
}

async function pollStatus(taskId) {
  try {
    const r = await fetch('/api/status/' + taskId);
    const j = await r.json();
    if (!j.ok) { stopPoll(); showResult('err', '<span class="tag">[ERR]</span>' + escapeHtml(j.error)); return; }
    barChars.textContent = renderBar(j.progress);
    stageText.textContent = j.stage || '';
    if (j.status === 'done') {
      stopPoll();
      showResult('ok',
        '<span class="tag">[OK]</span>fetch complete' +
        '<div class="line"><span class="k">title</span>' + escapeHtml(j.title) + '</div>' +
        '<div class="line"><span class="k">workId</span>' + j.work_id + '</div>' +
        '<div class="line"><span class="k">via</span>' + j.source + '</div>' +
        '<a class="dl-btn" href="/download/' + j.file_id + '">download zip</a>'
      );
      goBtn.disabled = false;
      goBtn.textContent = '[ DOWNLOAD ]';
      loadHistory();
    } else if (j.status === 'error') {
      stopPoll();
      showResult('err', '<span class="tag">[ERR]</span>' + escapeHtml(j.error || 'unknown'));
      goBtn.disabled = false;
      goBtn.textContent = '[ DOWNLOAD ]';
    }
  } catch (_) {}
}

function stopPoll() {
  if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
}

goBtn.addEventListener('click', start);
urlInput.addEventListener('keydown', e => { if (e.key === 'Enter') start(); });

if (window.__disclaimer_skipped) {
  loadHistory();
} else {
  window.addEventListener('__disclaimer_closed', loadHistory);
}
</script>
</body>
</html>
"""


# ============== 启动入口 ==============
def _start_server() -> None:
    """
    用 Waitress 启动 (生产级 WSGI server, 无 dev server 警告, 多线程稳定)。
    如果 Waitress 没装 (比如 requirements.txt 装一半), 兜底回 Flask dev server。
    """
    try:
        from waitress import serve
    except ImportError:
        log.warning("未安装 waitress, 回退到 Flask dev server "
                    "(如需消除 dev server 警告, 请运行: pip install waitress)")
        app.run(host=HOST, port=PORT, debug=False, threaded=True)
        return

    # 关掉 waitress 自己的 access log — 我们用 logging.info 统一打
    logging.getLogger("waitress").setLevel(logging.WARNING)
    log.info("使用 Waitress 启动 (生产 WSGI server)")
    # expose=False: 不需要把所有 IP 头透传, 我们是本机
    # threads=4: 4 个工作线程, 避免下载大文件时阻塞其他请求
    serve(app, host=HOST, port=PORT, threads=4, expose_tracebacks=False)


def main():
    DOWNLOADS_DIR.mkdir(parents=True, exist_ok=True)
    TASK_TMP_DIR.mkdir(parents=True, exist_ok=True)

    # 启动时清一次
    cleanup_expired()

    # 后台清理线程
    threading.Thread(target=cleanup_loop, daemon=True, name="cleanup").start()

    # 0.0.0.0 是绑定地址 (监听所有网卡), 但浏览器打开时要用 127.0.0.1
    display_host = "127.0.0.1" if HOST == "0.0.0.0" else HOST
    print("=" * 50)
    print(f"  Muse AI 下载器已启动")
    print(f"  打开:    http://{display_host}:{PORT}")
    print(f"  绑定:    {HOST}:{PORT}  (所有网卡)")
    print(f"  下载目录: {DOWNLOADS_DIR}")
    print(f"  保留天数: {KEEP_DAYS} 天")
    print("=" * 50)
    _start_server()


if __name__ == "__main__":
    main()
