#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* double word (8) alignment */
#define ALIGNMENT 8

/* 计算要分配的对齐后的内存大小*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
/* 将size_t大小也对齐到8*/
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*  字节大小规定*/ 
#define WSIZE 4
#define DSIZE 8

/*  一次扩4096字节东西*/
#define CHUNKSIZE (1 << 12)

/*  能返回的最小的块的大小*/
#define MINBLOCK (2 * DSIZE)

#define NLISTS 32               /* 册子数number of lists */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 通过看size最后一位看看有没有被占用*/
#define PACK(size, alloc) ((size) | (alloc))

/* 拿到的是这个指针解引用的东西本身 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

/* read the size and the allocated flag out of the word at address p 
这个size实际上是整个块的大小，不是payload区域的大小*/
#define GET_SIZE(p) (GET(p) & ~0x7u)
#define GET_ALLOC(p) (GET(p) & 0x1u)

/* bp是一个块指针，通过块指针直接拿到头的描述，和脚的描述 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 通过块指针，根据本快的大小得知之前和之后的块在哪里*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
/* 通过脚就能知道前一个有多大了*/
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))


/* 通过块指针拿到这个块的前后两个的链接，方便同一桶的互相跳转，同时桶方便进行电话号码的更改*/
#define PREV_LINK(bp) (*(int *)(bp))
#define NEXT_LINK(bp) (*(int *)((char *)(bp) + WSIZE))

/* 把块指针变成一个偏移量，省下指针的内存*/
#define OFFSET(bp) ((int)((char *)(bp) - (char *)mem_heap_lo()))
/* 把偏移量又变成块指针，相当于指针的替代品 使用这个就能把偏移量转化为一个相对于堆的起点的指针*/
#define ATPTR(off) ((char *)mem_heap_lo() + (off))

/* 堆指针，需要init*/
static char *heap_listp = NULL;
static int free_lists[NLISTS];  /* 每本册子的第一条，索引到的地方是一个偏移量而不是一个指针，这个偏移量需要使用ATPTR */

static void *extend_heap(size_t words);  /*声明一个函数，作用是扩展堆的大小*/
static void *coalesce(void *bp);  /* 作用是拼接两块，他会判断左右两边和自己的大小*/
static void *find_fit(size_t asize);  /* 找到适合自己的内存大小*/
static void place(void *bp, size_t asize); /* 放置，找到合适的地方后搬家落脚，并处理一系列手续*/
static size_t adjust(size_t size);  /* 判断大小应该对齐到哪里的，这个会处理最小分配地址问题，就不用上面的Align了*/
static int class_of(size_t size);
static void list_insert(void *bp);
static void list_remove(void *bp);


/* 初始化应该有的功能是，维护表，分配一个chunk大小的堆并拿到堆的指针，注意chunk是字节，要转化为字（）*/
int mm_init(void) {
    int i;
    for (i = 0; i < NLISTS; i++)
        free_lists[i] = 0;
        //先申请16字节为最小的块大小
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            // 对齐用的 4 字节 
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 序言块或说假货位：头便签 
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 假货位：尾便签，全部占用，为的是让第一个块能有个左邻居 
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 结尾块头：到此为止：长度 0 
    heap_listp += (2 * WSIZE);   //移动到序言的脚，方便nextblock
    //直接进行扩展到4kb，不过这一步扩容会把新的堆顶地址挪到结尾快后，
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
  }

void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    asize = adjust(size);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
/* 只是修改了标签并合并就行*/
void mm_free(void *ptr) {
    size_t size;

    if (ptr == NULL)
        return;

    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}
/* 要判断的很多，可以变短，可以变长，变长可以靠合并，可以靠扩大堆，可以选择直接再扩大堆，把东西都搬进来*/
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize;
    size_t asize;
    size_t csize;   //current size
    size_t nsize;
    size_t copySize;
    size_t total;
    char *next;
    char *rest;
    char *newptr;

    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    csize = GET_SIZE(HDRP(ptr));
    oldsize = csize - DSIZE;
    asize = adjust(size);

    if (asize <= csize) {                       /* 变短：原地把尾巴切掉 */
        if (csize - asize >= MINBLOCK) {
            PUT(HDRP(ptr), PACK(asize, 1));     //先改变自己的长度，方便改脚的位置
            PUT(FTRP(ptr), PACK(asize, 1));
            rest = NEXT_BLKP(ptr);
            PUT(HDRP(rest), PACK(csize - asize, 0)); //一定是八字节对齐的，不用管，一定显示不占用
            PUT(FTRP(rest), PACK(csize - asize, 0));
            coalesce(rest);
        }
        return ptr;
    }

    next = NEXT_BLKP(ptr);
    nsize = GET_SIZE(HDRP(next));

    if (nsize == 0) {                           /* 自己就在走廊最末尾：往后接 */
        if (mem_sbrk((int)(asize - csize)) == (void *)-1)
            return NULL;
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
        return ptr;
    }

    if (!GET_ALLOC(HDRP(next)) && csize + nsize >= asize) {
        list_remove(next);                      /* 把右边的空段吞进来 */
        total = csize + nsize;
        if (total - asize >= MINBLOCK) {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            rest = NEXT_BLKP(ptr);
            PUT(HDRP(rest), PACK(total - asize, 0));
            PUT(FTRP(rest), PACK(total - asize, 0));
            coalesce(rest);
        } else {
            PUT(HDRP(ptr), PACK(total, 1));
            PUT(FTRP(ptr), PACK(total, 1));
        }
        return ptr;
    }

    if ((newptr = mm_malloc(size)) == NULL)     /* 只能搬家 */
        return NULL;
    copySize = (size < oldsize) ? size : oldsize;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
  }

/* 计算请求多少字节  */
static size_t adjust(size_t size) {
    if (size <= DSIZE)
        return MINBLOCK;
    return DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
}

/* 为要找的分册16..128 每8字节一本（0..14）更大的每翻一倍一本 */
static int class_of(size_t size) {
    int i = 15;
    //128以下的（2的七次方），都可以靠移位得到number of list 16到128都是每次加8的桶 
    if (size <= 128)
        return (int)((size - MINBLOCK) >> 3);
    size >>= 7;
    //超过128的每次就该翻大桶码了
    while (size > 1) {
        size >>= 1;
        i++;
    }
    return i < NLISTS ? i : NLISTS - 1;
}

/* 头插这个块，拿到一个块，把这个块分桶，让这个块成为这一桶的第一个，他前面没有东西，后面指向原来的第一个，如果原来的第一个不是0的话，原来的第一个的前一个也得指向他*/
static void list_insert(void *bp) {
    int i = class_of(GET_SIZE(HDRP(bp)));
    PREV_LINK(bp) = 0;
    NEXT_LINK(bp) = free_lists[i];
    if (free_lists[i] != 0)
        //如果这一桶本来就放着有东西，（那通过这桶的偏移量得到的指针去索引得到的链接，就要变成这个的偏移量）
        PREV_LINK(ATPTR(free_lists[i])) = OFFSET(bp);
    //这个才是真正对表进行修改，前面都是在修改指针
    free_lists[i] = OFFSET(bp);
}

/* 删去头插的东西，回归原来的设置，如果是第一个就删除自己，如果不是第一个，就改变前面的指针指向后面*/
static void list_remove(void *bp) {
    int i = class_of(GET_SIZE(HDRP(bp)));
    int prev = PREV_LINK(bp);
    int next = NEXT_LINK(bp);
    if (prev != 0)
        NEXT_LINK(ATPTR(prev)) = next;
    else
        free_lists[i] = next;
    if (next != 0)
        PREV_LINK(ATPTR(next)) = prev;
}

/* 这里是根据需要的大小，把堆顶移动到结尾块，并且进行初始化，应该有以下功能：拿到新堆地址，填充头和尾和站位，由于我们保存的一直是偏移量，所以我们不用担心东西的指针都错乱了*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    //还是需要检查以下是否对齐的
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk((int)size)) == (void *)-1)
        return NULL;
    //现在bp总之应该是在结尾块后，可以正常用函数拿到之前结尾快的头进行更改，总之让这个结尾块变成一块普通的块了
    //puts第一个是槽位，第二个是放的值，值是一个四字节的
    PUT(HDRP(bp), PACK(size, 0));  //覆写后新块的头是4kb的大小
    PUT(FTRP(bp), PACK(size, 0));  //一直在4kb的末尾写footer
    //这个块实际上使用了原有区域的4字节，所以这4kb的空间，还有地方写4字节的结尾块头的内容
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp); //这里会加入表的
}

/* 拿到块指针的前后的链接的占用情况，拿到自己的大小，*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    char *prev;
    char *next;
    if (prev_alloc && next_alloc) {
        /* 左右都有占用，不用拼在一块 */
    } 
        /* 有占用的话，拿到大小，移除别人对他的指向，修改大小，并且看看头尾需不需要动*/
    else if (prev_alloc && !next_alloc) {
        next = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(next));
        list_remove(next);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else if (!prev_alloc && next_alloc) {
        prev = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(prev));
        list_remove(prev);
        bp = prev;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } 
    else {
        prev = PREV_BLKP(bp);
        next = NEXT_BLKP(bp);
        size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
        list_remove(prev);
        list_remove(next);
        bp = prev;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //表要插入全新的他
    list_insert(bp);
    return bp;
}
/* 在桶里找合适的，从第一个开始找，如果一直找不到就用后一个册子里直接拿第一个就行，*/
static void *find_fit(size_t asize) {
    int c = class_of(asize);
    int i;
    for (i = c; i < NLISTS; i++) {
        int off = free_lists[i];
        if (off == 0)
            continue;
        if (i == c) {                           /* 同一本册子里可能有偏小的段 */
            for (; off != 0; off = NEXT_LINK(ATPTR(off)))
                if (GET_SIZE(HDRP(ATPTR(off))) >= asize)
                    return ATPTR(off);
        } 
        else {
            return ATPTR(off);                  /* 更靠后的册子，第一条一定够大 */
        }
    }
    return NULL;
}
/* 这个是往块指针里放东西，放了东西就被占用了，同时要从表里移除自己，然后重新设置自己的个人信息*/
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    char *rest;
    list_remove(bp);
    if (csize - asize >= MINBLOCK) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        rest = NEXT_BLKP(bp);
        PUT(HDRP(rest), PACK(csize - asize, 0));
        PUT(FTRP(rest), PACK(csize - asize, 0));
        list_insert(rest);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}