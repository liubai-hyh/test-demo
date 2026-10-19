# 桌面宠物互动系统

一个基于 Python + Tkinter 的桌面宠物，支持 GIF 动画、点击互动、喂食、QQ 音乐控制与语音指令。

## 环境准备

- Python 3.8 及以上
- 安装依赖：

```bash
pip install -r requirements.txt
```

## 启动

双击 `start.bat`，或在命令行执行：

```bash
python main.py
```

## 功能

| 操作 | 效果 |
| --- | --- |
| 左键点击 | 弹出互动台词 |
| 左键拖拽 | 移动宠物，释放时带惯性 |
| 右键点击 | 打开功能菜单（喂食、GIF 控制、音乐、语音等） |
| 说出「小白」 | 唤醒语音控制 |

## 语音功能配置

语音识别依赖百度智能云，需要三项凭据。程序不会在仓库里保存真实密钥，请按以下步骤自行配置：

1. 复制 `local_secret.example.py`，重命名为 `local_secret.py`
2. 填入你的 `BAIDU_APP_ID`、`BAIDU_API_KEY`、`BAIDU_SECRET_KEY`
3. 保存即可，`local_secret.py` 已在 `.gitignore` 中，不会被提交

没有配置也能正常启动，只是语音识别不可用。

## 注意事项

- `gif/` 目录需包含 `pet1.gif`、`pet2.gif`、`angry_pet.gif` 三个动画文件
- QQ 音乐控制需安装默认路径的 QQ 音乐
- 语音控制需确保麦克风可用
