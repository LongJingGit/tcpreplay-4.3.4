# tcpreplay

## 安装

### 直接使用 yum 安装

```sh
yum -y install epel-release
yum -y install tcpreplay
```

### 使用源码编译安装

```sh
http://tcpreplay.appneta.com/wiki/installation.html#downloads
```

```sh
./configure
make
make install
```

如果执行 ./configure 失败，则先安装 libpcap

```sh
yum install libpcap-devel
```

如果需要使用 debug 版本进行调试，则需要将 configure 中的优化级别改为 -O0

```sh
Line 5445: CFLAGS="-g -O0"
```

## 使用

