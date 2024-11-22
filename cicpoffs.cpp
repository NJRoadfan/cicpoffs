/*
 * Copyright (c) 2020 Adler Neves <adlerosn@gmail.com>
 * Copyright (c) 2023 Bruno Gazotti <bgazotti@gmail.com>
 * 
 * CICPOFFS is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation version 2 of the License.
 *
 * User context switching when using "-o allow_other"
 * adapted from CIOPFS v0.4.
 * (c) 2008 Marc Andre Tanner <mat at brain-dump dot org>
 * (c) 2001-2007 Miklos Szeredi <miklos@szeredi.hu>
 */

#include "cicpoffs.hpp"
#include "cicpps.hpp"
extern "C"{
#include <errno.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <grp.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>
#include <dirent.h>
#include <sys/types.h>
#include <sys/xattr.h>
#include <fcntl.h>
#include <sys/time.h>
}

#define VERSION "0.0.2"

extern bool single_threaded;

static struct fuse_operations operations = {
	.getattr = fuse_fn_getattr,
	.readlink = fuse_fn_readlink,
	// .getdir = <unimplemented> - deprecated,
	.mknod = fuse_fn_mknod,
	.mkdir = fuse_fn_mkdir,
	.unlink = fuse_fn_unlink,
	.rmdir = fuse_fn_rmdir,
	.symlink = fuse_fn_symlink,
	.rename = fuse_fn_rename,
	.link = fuse_fn_link,
	.chmod = fuse_fn_chmod,
	.chown = fuse_fn_chown,
	.truncate = fuse_fn_truncate,
	//.utime = fuse_fn_utime,
	.open = fuse_fn_open,
	.read = fuse_fn_read,
	.write = fuse_fn_write,
	.statfs = fuse_fn_statfs,
	.flush = fuse_fn_flush,
	.release = fuse_fn_release,
	.fsync = fuse_fn_fsync,
	.setxattr = fuse_fn_setxattr,
	.getxattr = fuse_fn_getxattr,
	.listxattr = fuse_fn_listxattr,
	.removexattr = fuse_fn_removexattr,
	.opendir = fuse_fn_opendir,
	.readdir = fuse_fn_readdir,
	.releasedir = fuse_fn_releasedir,
	// .fsyncdir = fuse_fn_fsyncdir,
	.init = fuse_fn_init,
	.destroy = fuse_fn_destroy,
	.access = fuse_fn_access,
	.create = fuse_fn_create,
	//.ftruncate = fuse_fn_ftruncate,
	//.fgetattr = fuse_fn_fgetattr,
	.utimens = fuse_fn_utimens,
	//.bmap = <unimplemented> - not for block devices,
	//.ioctl = fuse_fn_ioctl,
	//.poll = fuse_fn_poll,
	//.flock = fuse_fn_flock,
	.fallocate = fuse_fn_fallocate,
};

static char* read_source_directory = NULL;

static char* argv0 = NULL;

static void stderr_print(const char* msg){
	fprintf(stderr, "[%s] %s\n", argv0, msg);
};

static void ignore_print(const char* msg){};

static void (*logmsg) (const char* msg) = ignore_print;

/* Returns the supplementary group IDs of a calling process which
 * isued the file system operation.
 *
 * As indicated by Miklos Szeredi the group list is available in
 *
 *   /proc/$PID/task/$TID/status
 *
 * and fuse supplies TID in get_fuse_context()->pid.
 *
 * Jean-Pierre Andre found out that the same information is also
 * available in
 *
 *   /proc/$TID/task/$TID/status
 *
 * which is used in this implementation.
 */

static size_t get_groups(pid_t pid, gid_t **groups)
{
	static char key[] = "\nGroups:\t";
	char filename[64], buf[2048], *s, *t, c = '\0';
	int fd, num_read, matched = 0;
	size_t n = 0;
	gid_t *gids, grp = 0;

	sprintf(filename, "/proc/%u/task/%u/status", pid, pid);
	fd = open(filename, O_RDONLY);
	if (fd == -1)
		return 0;

	for (;;) {
		if (!c) {
			num_read = read(fd, buf, sizeof(buf) - 1);
			if (num_read <= 0) {
				close(fd);
				return 0;
			}
			buf[num_read] = '\0';
			s = buf;
		}

		c = *s++;

		if (key[matched] == c) {
			if (!key[++matched])
				break;

		} else
			matched = (key[0] == c);
	}

	close(fd);
	t = s;
	n = 0;

	while (*t != '\n') {
		if (*t++ == ' ')
			n++;
	}

	if (n == 0)
		return 0;

	*groups = gids = (gid_t*) malloc(n * sizeof(gid_t));
	if (!gids)
		return 0;
	n = 0;

	while ((c = *s++) != '\n') {
		if (c >= '0' && c <= '9')
			grp = grp*10 + c - '0';
		else if (c == ' ') {
			gids[n++] = grp;
			grp = 0;
		}
	}

	return n;
}

/* This only works when the filesystem is mounted by root and fuse
 * operates in single threaded mode. Because the euid/egid are stored
 * per process this would otherwise cause all sorts of race condidtions
 * and security issues when multiple users access the file system
 * simultaneously.
 */

static void enter_user_context_effective()
{
	gid_t *groups;
	size_t ngroups;
	struct fuse_context *c = fuse_get_context();

	if (!single_threaded || getuid())
		return;
	if ((ngroups = get_groups(c->pid, &groups))) {
		setgroups(ngroups, groups);
		free(groups);
	}

	setegid(c->gid);
	seteuid(c->uid);
}

static void leave_user_context_effective()
{
	if (!single_threaded || getuid())
		return;

	seteuid(getuid());
	setegid(getgid());
}

/* access(2) checks the real uid/gid not the effective one
 * we therefore switch them if run as root and in single
 * threaded mode.
 *
 * The real uid/gid are stored per process which is why we
 * can't change them in multithreaded mode. This would lead
 * to all sorts of race conditions and security issues when
 * multiple users access the file system simultaneously.
 *
 */

static void enter_user_context_real()
{
	gid_t *groups;
	size_t ngroups;
	struct fuse_context *c = fuse_get_context();

	if (!single_threaded || geteuid())
		return;
	if ((ngroups = get_groups(c->pid, &groups))) {
		setgroups(ngroups, groups);
		free(groups);
	}
	setregid(c->gid, -1);
	setreuid(c->uid, -1);
}

static void leave_user_context_real()
{
	if (!single_threaded || geteuid())
		return;

	setuid(geteuid());
	setgid(getegid());
}

void* (fuse_fn_init)        (struct fuse_conn_info* conn, struct fuse_config* cfg){
	struct stat st;
	if(stat(read_source_directory, &st)){
		logmsg("Source does not exist.");
		exit(ENOENT);
	}
	if(read_source_directory[0]!='/'){
		logmsg("Path must be absolute.");
		exit(ENOENT);
	}
	cfg->use_ino = 1;
        /* Pick up changes from lower filesystem right away. This is
           also necessary for better hardlink support. When the kernel
           calls the unlink() handler, it does not know the inode of
           the to-be-removed entry and can therefore not invalidate
           the cache of the associated inode - resulting in an
           incorrect st_nlink value being reported for any remaining
           hardlinks to this inode. */
        cfg->entry_timeout = 0;
        cfg->attr_timeout = 0;
        cfg->negative_timeout = 0;
	return NULL;
};

void  (fuse_fn_destroy)     (void* private_data){
	return;
};

int   (fuse_fn_getattr)     (const char* path, struct stat* stbuf, struct fuse_file_info* fi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = stat(correctpath, stbuf);
	leave_user_context_effective();
	free((void*) correctpath);
	if(retval==-1) return -errno;
	return retval;
};

int   (fuse_fn_readlink)    (const char* path, char* buf, size_t size){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = readlink(correctpath, buf, size);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_mknod)       (const char* path, mode_t mode, dev_t rdev){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = mknod(correctpath, mode, rdev);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_mkdir)       (const char* path, mode_t mode){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = mkdir(correctpath, mode);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_unlink)      (const char* path){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = unlink(correctpath);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_rmdir)       (const char* path){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = rmdir(correctpath);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_symlink)     (const char* to, const char* from){
	const char* correctfrom = correct_case_sensitivity_for(read_source_directory, from);
	enter_user_context_effective();
	int retval = symlink(to, correctfrom);
	leave_user_context_effective();
	free((void*) correctfrom);
	return retval;
};

// flag behavior is absolutely ignored
int   (fuse_fn_rename)      (const char* from, const char* to, unsigned int flags){
	const char* correctfrom = correct_case_sensitivity_for(read_source_directory, from);
	const char* correctto = correct_case_sensitivity_for(read_source_directory, to);
	const char* sameto = return_to_path(read_source_directory, to);
	enter_user_context_effective();
	int retval;
	//Check if user is using the same filename, but with different case ex: "my file" to "My file"
	if (!strcmp(correctfrom,correctto))
	{
		retval = rename(correctfrom, sameto);
	}
	else
	{
		retval = rename(correctfrom, correctto);
	}
	leave_user_context_effective();
	free((void*) correctfrom);
	free((void*) correctto);
	free((void*) sameto);
	return retval;
};

int   (fuse_fn_link)        (const char* from, const char* to){
	const char* correctfrom = correct_case_sensitivity_for(read_source_directory, from);
	const char* correctto = correct_case_sensitivity_for(read_source_directory, to);
	enter_user_context_effective();
	int retval = link(correctfrom, correctto);
	leave_user_context_effective();
	free((void*) correctfrom);
	free((void*) correctto);
	return retval;
};

int   (fuse_fn_chmod)       (const char* path, mode_t mode, struct fuse_file_info* fi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = chmod(correctpath, mode);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_chown)       (const char* path, uid_t uid, gid_t gid, struct fuse_file_info*){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = chown(correctpath, uid, gid);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_truncate)    (const char* path, off_t off, struct fuse_file_info*){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = truncate(correctpath, off);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

/** int   (fuse_fn_utime)       (const char* path, struct utimbuf* buf){
*	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
*	int retval = utime(correctpath, buf);
*	free((void*) correctpath);
*	return retval;
};*/

int   (fuse_fn_open)        (const char* path, struct fuse_file_info* ffi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int fd = open(correctpath, ffi->flags);
	leave_user_context_effective();
	free((void*) correctpath);
	ffi->fh = fd;
	return (fd==-1) ? -errno : 0;
};

int   (fuse_fn_read)        (const char* path, char* buf, size_t size, off_t off, struct fuse_file_info* ffi){
	return pread(ffi->fh, buf, size, off);
};

int   (fuse_fn_write)       (const char* path, const char* buf, size_t size, off_t off, struct fuse_file_info* ffi){
	return pwrite(ffi->fh, buf, size, off);
};

int   (fuse_fn_statfs)      (const char* path, struct statvfs* svfs){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = statvfs(correctpath, svfs);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_flush)       (const char* path, struct fuse_file_info* ffi){
	return close(dup(ffi->fh));
};

int   (fuse_fn_release)     (const char* path, struct fuse_file_info* ffi){
	return close(ffi->fh);
};

int   (fuse_fn_fsync)       (const char* path, int data_sync, struct fuse_file_info* ffi){
	#ifdef HAVE_FDATASYNC
	if(data_sync)
		return fdatasync(ffi->fh);
	else
	#endif
		return fsync(ffi->fh);
};

int   (fuse_fn_setxattr)    (const char* path, const char* key, const char* value, size_t size, int flags){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = lsetxattr(correctpath, key, value, size, flags);
	leave_user_context_effective();
	free((void*) correctpath);
	if(retval==-1) return -errno;
	return retval;
};

int   (fuse_fn_getxattr)    (const char* path, const char* key, char* value, size_t size){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = lgetxattr(correctpath, key, value, size);
	leave_user_context_effective();
	free((void*) correctpath);
	if(retval==-1) return -errno;
	return retval;
};

int   (fuse_fn_listxattr)   (const char* path, char* list, size_t size){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = llistxattr(correctpath, list, size);
	leave_user_context_effective();
	free((void*) correctpath);
	if(retval==-1) return -errno;
	return retval;
};

int   (fuse_fn_removexattr) (const char* path, const char* key){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = lremovexattr(correctpath, key);
	leave_user_context_effective();
	free((void*) correctpath);
	if(retval==-1) return -errno;
	return retval;
};

int   (fuse_fn_opendir)     (const char* path, struct fuse_file_info* ffi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	DIR* dp = opendir(correctpath);
	leave_user_context_effective();
	free((void*) correctpath);
	ffi->fh = (uintptr_t) dp;
	return dp==NULL ? -errno : 0;
};

int   (fuse_fn_readdir)     (const char* path, void* buf, fuse_fill_dir_t filler, off_t off, struct fuse_file_info* ffi, enum fuse_readdir_flags flags){
	DIR* dp = (DIR*) ffi->fh;
	if(!dp) return -EBADF;
	seekdir(dp, off);
	struct dirent *de;
	while((de = readdir(dp)) != NULL){
		struct stat st;
		st.st_ino = de->d_ino;
		st.st_mode = de->d_type << 12;
		if (filler(buf, de->d_name, &st, telldir(dp), FUSE_FILL_DIR_PLUS)) break;
	}
	return 0;
};

int   (fuse_fn_releasedir)  (const char* path, struct fuse_file_info* ffi){
	if(ffi->fh)
		closedir((DIR*)(uintptr_t) ffi->fh);
	ffi->fh = 0;
	return 0;
};

// int   (fuse_fn_fsyncdir)    (const char* path, int isdatasync, struct fuse_file_info* ffi){
// 	return ENOSYS;
// };

int   (fuse_fn_access)      (const char* path, int mode){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_real();
	int retval = access(correctpath, mode);
	leave_user_context_real();
	free((void*) correctpath);
	return retval;
};

int   (fuse_fn_create)      (const char* path, mode_t mode, struct fuse_file_info* ffi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int fd = open(correctpath, ffi->flags, mode);
	leave_user_context_effective();
	free((void*) correctpath);
	if(fd==-1) return -errno;
	ffi->fh = fd;
	return 0;
};

int   (fuse_fn_ftruncate)   (const char* path, off_t off, struct fuse_file_info* ffi){
	enter_user_context_effective();
	int retval = ftruncate(ffi->fh, off);
	leave_user_context_effective();
	return retval;
};

int   (fuse_fn_fgetattr)    (const char* path, struct stat* st, struct fuse_file_info* ffi){
	enter_user_context_effective();
	int retval = fstat(ffi->fh, st);
	if(retval==-1) return -errno;
	leave_user_context_effective();
	return retval;
};

int   (fuse_fn_utimens)     (const char* path, const struct timespec ts[2], struct fuse_file_info* ffi){
	const char* correctpath = correct_case_sensitivity_for(read_source_directory, path);
	enter_user_context_effective();
	int retval = utimensat(0,correctpath,ts,AT_SYMLINK_NOFOLLOW);
	leave_user_context_effective();
	free((void*) correctpath);
	return retval;
};

// int   (fuse_fn_ioctl)       (const char* path, int cmd, void* arg, struct fuse_file_info* ffi, unsigned int flags, void* data){
// 	return ENOSYS;
// };

// int   (fuse_fn_poll)        (const char* path, struct fuse_file_info* ffi, struct fuse_pollhandle* ph, unsigned* reventsp){
// 	return ENOSYS;
// };

// int   (fuse_fn_write_buf)   (const char* path, struct fuse_bufvec* buf, off_t off, struct fuse_file_info* ffi){
// 	return ENOSYS;
// };

// int   (fuse_fn_read_buf)    (const char* path, struct fuse_bufvec** buf, size_t size, off_t off, struct fuse_file_info* ffi){
// 	return ENOSYS;
// };

// int   (fuse_fn_flock)       (const char* path, struct fuse_file_info*, int){
// 	return ENOSYS;
// };

int   (fuse_fn_fallocate)   (const char* path, int mode, off_t off, off_t len, struct fuse_file_info* ffi){
	enter_user_context_effective();
	int retval = fallocate(ffi->fh, mode, off, len);
	leave_user_context_effective();
	return retval;
};
