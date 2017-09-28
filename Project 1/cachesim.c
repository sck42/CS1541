#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cachesim.h"
#include <math.h>
#include <time.h>

/*
Usage:
	./cachesim -I 4096:1:2:R -D 1:4096:2:4:R:B:A -D 2:16384:4:8:L:T:N trace.txt

The -I flag sets instruction cache parameters. The parameter after looks like:
	4096:1:2:R
This means the I-cache will have 4096 blocks, 1 word per block, with 2-way
associativity.

The R means Random block replacement; L for that item would mean LRU. This
replacement scheme is ignored if the associativity == 1.

The -D flag sets data cache parameters. The parameter after looks like:
	1:4096:2:4:R:B:A

The first item is the level and must be 1, 2, or 3.

The second through fourth items are the number of blocks, words per block, and
associativity like for the I-cache. The fifth item is the replacement scheme,
just like for the I-cache.

The sixth item is the write scheme and can be:
	B for write-Back
	T for write-Through

The seventh item is the allocation scheme and can be:
	A for write-Allocate
	N for write-No-allocate

The last argument is the filename of the memory trace to read. This is a text
file where every line is of the form:
	0x00000000 R
A hexadecimal address, followed by a space and then R, W, or I for data read,
data write, or instruction fetch, respectively.
*/

/* These global variables will hold the info needed to set up your caches in
your setup_caches function. Look in cachesim.h for the description of the
CacheInfo struct for docs on what's inside it. Have a look at dump_cache_info
for an example of how to check the members. */
static CacheInfo icache_info;
static CacheInfo dcache_info[3];
//static IMetaData iMeta;
//static DMetaData dMeta;

static MetaData** iCache;
static MetaData** dCache;
int dallocate;
int wordIndex;
int numWrites;
int numWordsWritten;

//Instruction Reads
int readMisses;
int readHits;
int numReads;
int compul;
int conflict;
int capacity;

//Data Reads
int readMissesD;
int readHitsD;
int numReadsD;
int compulD;
int conflictD;
int capacityD;

//Writes
int compulW;
int conflictW;
int capacityW;
int wHits;
int wMisses;
int numWordsRead;

void setUpVariables(MetaData** a, CacheInfo cache_info)
{
	readMisses = 0;
	readHits = 0;
	numReads = 0;
	compul = 0;
	conflict = 0;
	capacity = 0;
	compulW = 0;
	conflictW = 0;
	capacityW = 0;
	numWrites = 0;
	numWordsWritten = 0;
	wHits = 0;
	wMisses = 0;
	numWordsRead = 0;
	int numBlocks = cache_info.num_blocks;
	int associativity = cache_info.associativity;
	for(int j = 0; j < (numBlocks/associativity); j++)
	{
		for(int i = 0; i < associativity; i++)
		{
			a[j][i].tag = 0;
			a[j][i].valid = 0;
			a[j][i].dirty = 0;
			a[j][i].LRU = 0;
		}
	}
}

void setup_caches()
{
	/* Set up your caches here! */
	srand(1000);//(unsigned int)time(NULL));
	int numBlocks = icache_info.num_blocks;
	int associativity = icache_info.associativity;
	int numRows = numBlocks/associativity;
	iCache = calloc(sizeof(MetaData*), numRows);
	for(int i = 0; i < numRows; i++)
	{
		iCache[i] = calloc(sizeof(MetaData), associativity);
	}
	setUpVariables(iCache, icache_info);

	dallocate = 0;
	//Only allocate dCache if dCache data was given. 
	if(dcache_info[0].associativity > 0)
	{
		dallocate = 1;
		numBlocks = dcache_info[0].num_blocks;
		associativity = dcache_info[0].associativity;
		numRows = numBlocks/associativity;
		dCache = calloc(sizeof(MetaData*), numRows);
		for(int i = 0; i < numRows; i++)
		{
			dCache[i] = calloc(sizeof(MetaData), associativity);

		}
		setUpVariables(dCache, dcache_info[0]);
	}

	/* This call to dump_cache_info is just to show some debugging information
	and you may remove it. */
	dump_cache_info();
}


//Increment the age of all elements in the block.
//Set the newest element to zero.
void fixLRU(int rowIndex, int indexToKeep, MetaData** cache, CacheInfo cache_info)
{
	for(int i = 0; i < cache_info.associativity; i++)
	{
		cache[rowIndex][i].LRU++;
	}

	cache[rowIndex][indexToKeep].LRU = 0;
}

//Randomly replace data.
int ranReplace(int rowIndex, MetaData** cache, CacheInfo cache_info, int tag)
{
	int newAssoIndex = rand() % (cache_info.associativity - 1);
	//Check if dirty even on reads 
	if(cache[rowIndex][newAssoIndex].dirty == 1)
		numWordsWritten += cache_info.words_per_block;
	cache[rowIndex][newAssoIndex].tag = tag;
	cache[rowIndex][newAssoIndex].valid = 1;
	cache[rowIndex][newAssoIndex].dirty = 0;
	fixLRU(rowIndex, newAssoIndex, cache, cache_info);
	return newAssoIndex;
}

//Find oldest data then replace it.
int lruReplace(int rowIndex, MetaData** cache, CacheInfo cache_info, int tag)
{
	int oldest = 0;
	int lruIndex = 0;
	for(int i = 0; i < cache_info.associativity; i++)
	{
		if(cache[rowIndex][i].LRU > oldest)
		{
			oldest = cache[rowIndex][i].LRU;
			lruIndex = i;
		}
	}
	
	//Check if dirty even on reads 
	if(cache[rowIndex][lruIndex].dirty == 1)
		numWordsWritten += cache_info.words_per_block;
	cache[rowIndex][lruIndex].tag = tag;
	cache[rowIndex][lruIndex].valid = 1;
	cache[rowIndex][lruIndex].dirty = 0;
	fixLRU(rowIndex, lruIndex, cache, cache_info);
	return lruIndex;
}


int isOpen(int rowIndex)
{
	//Look for an invalid block in the set. 
	for(int i = 0; i < dcache_info[0].associativity; i++)
	{
		if(dCache[rowIndex][i].valid == 0)
			return i;
	}
	return -1;
}

//Fill in the invalid block with the appropriate write/alloc scheme. 
void fillOpenSpace(int rowIndex, int openSpace, int numWordBlock, int tag)
{

	if(dcache_info[0].write_scheme == Write_WRITE_THROUGH)
	{
		//Over write the block in cache. Cache is consistent so the another copy is in memory.
		//Write to both cache and memory.
		if(dcache_info[0].allocate_scheme == Allocate_NO_ALLOCATE)
		{
			//Do nothing to the cache when no allocate. 
			numWordsWritten++;
			if(dcache_info[0].associativity == 1)
				conflictW++;
			else
				capacityW++;
		}
		else if(dcache_info[0].allocate_scheme == Allocate_ALLOCATE)
		{
			//Add number of words read then replace the cache. 
			//Write to memory the old word. 
			if(numWordBlock > 1)
			{
				numWordsRead += numWordBlock;
			}
			dCache[rowIndex][openSpace].tag = tag;
			dCache[rowIndex][openSpace].valid = 1;
			dCache[rowIndex][openSpace].dirty = 0;
			numWordsWritten++;
			compulW++;
			fixLRU(rowIndex, openSpace, dCache, dcache_info[0]);
		}
	}
	else if(dcache_info[0].write_scheme == Write_WRITE_BACK)
	{
		//Write the memory the words in the block and replace with new block. 
		dCache[rowIndex][openSpace].tag = tag;
		dCache[rowIndex][openSpace].valid = 1;
		dCache[rowIndex][openSpace].dirty = 1;
		compulW++;
		numWordsRead += numWordBlock;
		fixLRU(rowIndex, openSpace, dCache, dcache_info[0]);
	}
}
//Write to cache on the write hit. 
void performWrite(int rowIndex, int assoIndex)
{
	if(dcache_info[0].write_scheme == Write_WRITE_THROUGH)
	{
		//Write to memory and the Cache.
		numWordsWritten++;
	}
	else if(dcache_info[0].write_scheme == Write_WRITE_BACK)
	{
		//Write to Cache Normally Don't write to memory. Set dirty to one.
		dCache[rowIndex][assoIndex].dirty = 1;
	}
}
//Write to memory when a write miss other than compulsory miss occurs. 
void writeMem(int rowIndex, int index, MetaData** cache, CacheInfo cache_info, int tag)
{
	if(cache_info.write_scheme == Write_WRITE_BACK)
	{
		if(cache[rowIndex][index].dirty == 1)
		{
			numWordsWritten += cache_info.words_per_block; //if block is dirty, write it to memory then replace the cache block.
			cache[rowIndex][index].dirty = 0;
		}
		//If block is clean override the block and write to memory. 
		if(cache[rowIndex][index].dirty == 0)
		{
			cache[rowIndex][index].tag = tag;
			cache[rowIndex][index].valid = 1;
			cache[rowIndex][index].dirty = 1;
			fixLRU(rowIndex, index, cache, cache_info);
		}
		numWordsRead += cache_info.words_per_block;
		if(dcache_info[0].associativity == 1)
			conflictW++;
		else
			capacityW++;
	}
	else
	{
		//Write no alloc don't change the cache but write to memory. 
		if(cache_info.allocate_scheme == Allocate_NO_ALLOCATE)
		{
			numWordsWritten++;
			if(dcache_info[0].associativity == 1)
				conflictW++;
			else
				capacityW++;
		}
		else if(cache_info.allocate_scheme == Allocate_ALLOCATE)
		{
			//Add number of words read and write to memory the old word.
			//Replace the cache block with new data. 
			if(cache_info.words_per_block > 1)
			{
				numWordsRead += cache_info.words_per_block;
			}
			cache[rowIndex][index].tag = tag;
			cache[rowIndex][index].valid = 1;
			cache[rowIndex][index].dirty = 0;
			fixLRU(rowIndex, index, cache, cache_info);
			numWordsWritten++;
			if(dcache_info[0].associativity == 1)
				conflictW++;
			else
				capacityW++;
		}
	}

}
//Randomly replace data.
int ranReplaceD(int rowIndex, MetaData** cache, CacheInfo cache_info, int tag)
{
	int newAssoIndex = rand() % (cache_info.associativity - 1);
	writeMem(rowIndex, newAssoIndex, cache, cache_info, tag);
	return newAssoIndex;
}

//Find oldest data then replace it.
int lruReplaceD(int rowIndex, MetaData** cache, CacheInfo cache_info, int tag)
{
	int oldest = 0;
	int lruIndex = 0;
	for(int i = 0; i < cache_info.associativity; i++)
	{
		if(cache[rowIndex][i].LRU > oldest)
		{
			oldest = cache[rowIndex][i].LRU;
			lruIndex = i;
		}
	}
	writeMem(rowIndex, lruIndex, cache, cache_info, tag);
	return lruIndex;
}

//Look for address in the cache.
//If not found read from memory and count up the appropriate miss.
//If found increment number of hits.
void cacheAccess(addr_t address, MetaData** cache, CacheInfo cache_info, int whichCounts)
{
	int numWordBlock = cache_info.words_per_block;
	int numBlocks = cache_info.num_blocks;
	int wordBit = (int) ceil(log2(numWordBlock));
	int rowBit = (int) ceil(log2(numBlocks/cache_info.associativity));
	int tagBit = 32 - wordBit - rowBit - 2;
	int rowShift = wordBit + 2;
	int tagShift = wordBit + rowBit + 2;
	int rowMask = (1 << rowBit) - 1;
	int tagMask = (1 << tagBit) - 1;
	if(whichCounts)
		numReads++;
	else
		numReadsD++;
	//Find the rowIndex, associativity index and tag.
	int rowIndex = (address >> rowShift) & rowMask;
	int assoIndex = 0;
	int tag = (address >> tagShift) & tagMask;

	//If requested block is empty read from memory.
	//Compulsory Miss
	if(cache[rowIndex][assoIndex].valid == 0)
	{
		if(whichCounts)
			compul++;
		else
		{
			compulD++;
		}
		cache[rowIndex][assoIndex].tag = tag;
		cache[rowIndex][assoIndex].valid = 1;
		fixLRU(rowIndex, assoIndex, cache, cache_info);
		return;
	}
	else
	{
		//If requested block is found increment hit and fix lru.
		if(cache[rowIndex][assoIndex].tag == tag)
		{
			if(whichCounts)
				readHits++;
			else
				readHitsD++;
			fixLRU(rowIndex, assoIndex, cache, cache_info);
			return;
		}
		//If requested block is not found check other blocks in the associativity.
		else
		{
			if(cache_info.associativity == 1) //If directmapped than its a conflict miss. 
			{
				if(whichCounts)
					conflict++;
				else
					conflictD++;
				cache[rowIndex][0].tag = tag;
				cache[rowIndex][0].valid = 1;
			}
			else //If not direct mapped check other blocks in set. 
			{
				for(int i = 0; i < cache_info.associativity; i++)
				{
					if(cache[rowIndex][i].valid == 1)
					{
						if(cache[rowIndex][i].tag == tag) //If found in the set its a hit. 
						{
							fixLRU(rowIndex, i, cache, cache_info);
							if(whichCounts)
								readHits++;
							else
								readHitsD++;

							return;
						}
					}
					//Check for open space and replace if found. Empty block so compulsory miss. 
					else if(cache[rowIndex][i].valid == 0)
					{
						if(whichCounts)
							compul++;
						else
							compulD++;

						cache[rowIndex][i].tag = tag;
						cache[rowIndex][i].valid = 1;
						fixLRU(rowIndex, i, cache, cache_info);
						return;
					}
				}
				//If none of the associativity blocks match replace.
				//If open space is not found perform replacement scheme.
				if(whichCounts)
					capacity++;
				else
					capacityD++;
				if(cache_info.replacement == Replacement_RANDOM)
					ranReplace(rowIndex, cache, cache_info, tag);
				else if(cache_info.replacement == Replacement_LRU)
					lruReplace(rowIndex, cache, cache_info, tag);
			}
		}
	}
}
void dWrite(addr_t address)
{
	int numWordBlock = dcache_info[0].words_per_block;
	int numBlocks = dcache_info[0].num_blocks;
	int wordBit = (int) ceil(log2(numWordBlock));
	int rowBit = (int) ceil(log2(numBlocks/dcache_info[0].associativity));
	int tagBit = 32 - wordBit - rowBit - 2;
	int rowShift = wordBit + 2;
	int tagShift = wordBit + rowBit + 2;
	int rowMask = (1 << rowBit) - 1;
	int tagMask = (1 << tagBit) - 1;

	//Find the rowIndex, associativity index and tag.
	int rowIndex = (address >> rowShift) & rowMask;
	int assoIndex = 0;
	int tag = (address >> tagShift) & tagMask;
	numWrites++;
	if(dCache[rowIndex][assoIndex].valid == 1)
	{
		if(dCache[rowIndex][assoIndex].tag == tag) //Valid block and tag match == Hit
		{
			wHits++;
			performWrite(rowIndex, assoIndex);
			fixLRU(rowIndex, assoIndex, dCache, dcache_info[0]);
			return;
		}
		else //Valid block but tag doesn't match
		{
			if(dcache_info[0].associativity == 1) //Valid block, tag doesn't match and direct Mapped == conflict miss
			{
				writeMem(rowIndex, assoIndex, dCache, dcache_info[0], tag);
				return;
			}
			else //Valid block, tag doesn't match and associativity is greater than 1
			{
				//Check for tag or an open spaces in the other blocks in row
				//If tag is found its a hit
				for(int i = 1; i < dcache_info[0].associativity; i++)
				{
					if(dCache[rowIndex][i].valid == 1)
					{
						if(dCache[rowIndex][i].tag == tag)
						{
							wHits++;
							performWrite(rowIndex, i);
							fixLRU(rowIndex, i, dCache, dcache_info[0]);
							return;
						}
					}
				}

				int index = isOpen(rowIndex);
				if(index != -1) //Open space is found so compulsory miss.
				{
					fillOpenSpace(rowIndex, index, numWordBlock, tag);
					return;
				}
				//None of the associativity blocks match == capacity miss
				//Replace using the right method.
				else //No open space found so capacity miss.
				{
					if(dcache_info[0].replacement == Replacement_RANDOM)
						ranReplaceD(rowIndex, dCache, dcache_info[0], tag);
					else if(dcache_info[0].replacement == Replacement_LRU)
						lruReplaceD(rowIndex, dCache, dcache_info[0], tag);
					return;
				}
			}
		}
	}
	else //Valid is zero == compulsory miss, Replace block using the appropriate allocation scheme
	{
		fillOpenSpace(rowIndex, assoIndex, numWordBlock, tag);
		return;
	}
}

void handle_access(AccessType type, addr_t address)
{
	/* This is where all the fun stuff happens! This function is called to
	simulate a memory access. You figure out what type it is, and do all your
	fun simulation stuff from here. */

	switch(type)
	{
		case Access_I_FETCH:
			/* These prints are just for debugging and should be removed. */
			cacheAccess(address, iCache, icache_info, 1);
			break;
		case Access_D_READ:
			if(dallocate)
				cacheAccess(address, dCache, dcache_info[0], 0);
			break;
		case Access_D_WRITE:
			if(dallocate)
				dWrite(address);
			break;
	}
}

void print_statistics()
{
	/* Finally, after all the simulation happens, you have to show what the
	results look like. Do that here.*/

	readMisses = compul + conflict + capacity;
	wMisses = compulW + conflictW + capacityW; 
	int readDataMisses = compulD + conflictD + capacityD; 
	printf("I-cache Stats: \n");
	printf("Number of Reads: %30d\n", numReads);
	printf("Number of Words: %30d\n", readMisses * icache_info.words_per_block);
	printf("Read Misses:\n");
	printf("       Compulsory Miss: %23d\n", compul);
	printf("       Conflict Misses: %23d\n", conflict);
	printf("       Capacity Misses: %23d\n", capacity);
	printf("       Number of Misses: %22d\n", readMisses); 
	printf("Read Miss rate with Compulsory: %15.2f%%\n", ((double)readMisses/(double)numReads) * 100);
	readMisses -= compul; 
	printf("Read Miss rate without Compulsory: %12.2f%%\n", ((double)readMisses/(double)numReads) * 100);
	printf("\n\n");
	printf("L1 D-cache Stats:\n");
	printf("Number of Reads: %30d\n", numReadsD);
	printf("Number of Words Read: %25d\n", numWordsRead + (readDataMisses * dcache_info[0].words_per_block));
	printf("Number of Writes: %29d\n", numWrites);
	printf("Number of Words Writen: %23d\n", numWordsWritten);
	printf("Read Misses:\n");
	printf("       Compulsory Miss: %23d\n", compulD);
	printf("       Conflict Misses: %23d\n", conflictD);
	printf("       Capacity Misses: %23d\n", capacityD);
	printf("       Number of Misses: %22d\n", readDataMisses);
	if(numReadsD == 0){numReadsD = 1;} //In case not doing a write.
	printf("       Read Miss rate with Compulsory: %8.2f%%\n", ((double)readDataMisses/(double)numReadsD) * 100);
	readDataMisses -= compulD; 
	printf("       Read Miss rate without Compulsory: %5.2f%%\n", ((double)readDataMisses/(double)numReadsD) * 100);
	printf("Write Misses:\n");
	printf("       Compulsory Miss: %23d\n", compulW);
	printf("       Conflict Misses: %23d\n", conflictW);
	printf("       Capacity Misses: %23d\n", capacityW);
	printf("       Number of Misses: %22d\n", wMisses);
	if(numWrites == 0){numWrites = 1;} //In case not doing a write.
	printf("       Write Miss rate With Compulsory: %7.2f%%\n", ((double)wMisses/(double)numWrites) * 100 );	
	wMisses -= compulW; 
	printf("       Write Miss rate Without Compulsory: %3.2f%%\n", ((double)wMisses/(double)numWrites) * 100 );
}

/*******************************************************************************
*
*
*
* DO NOT MODIFY ANYTHING BELOW THIS LINE!
*
*
*
*******************************************************************************/

void dump_cache_info()
{
	int i;
	CacheInfo* info;

	printf("Instruction cache:\n");
	printf("\t%d blocks\n", icache_info.num_blocks);
	printf("\t%d word(s) per block\n", icache_info.words_per_block);
	printf("\t%d-way associative\n", icache_info.associativity);

	if(icache_info.associativity > 1)
	{
		printf("\treplacement: %s\n\n",
			icache_info.replacement == Replacement_LRU ? "LRU" : "Random");
	}
	else
		printf("\n");

	for(i = 0; i < 3 && dcache_info[i].num_blocks != 0; i++)
	{
		info = &dcache_info[i];

		printf("Data cache level %d:\n", i);
		printf("\t%d blocks\n", info->num_blocks);
		printf("\t%d word(s) per block\n", info->words_per_block);
		printf("\t%d-way associative\n", info->associativity);

		if(info->associativity > 1)
		{
			printf("\treplacement: %s\n", info->replacement == Replacement_LRU ?
				"LRU" : "Random");
		}

		printf("\twrite scheme: %s\n", info->write_scheme == Write_WRITE_BACK ?
			"write-back" : "write-through");

		printf("\tallocation scheme: %s\n\n",
			info->allocate_scheme == Allocate_ALLOCATE ?
			"write-allocate" : "write-no-allocate");
	}
}

void read_trace_line(FILE* trace)
{
    char line[100];
    addr_t address;
    char type;

    if(fgets(line, sizeof(line), trace) == NULL)
        return;

    if(sscanf(line, "0x%lx %c", &address, &type) < 2)
        return;

    switch(type)
    {
        case 'R': handle_access(Access_D_READ, address);  break;
        case 'W': handle_access(Access_D_WRITE, address); break;
        case 'I': handle_access(Access_I_FETCH, address); break;
        default:
            fprintf(stderr, "Malformed trace file: invalid access type '%c'.\n",
                type);
            exit(1);
            break;
    }
}

static void bad_params(const char* msg)
{
	fprintf(stderr, msg);
	fprintf(stderr, "\n");
	exit(1);
}

#define streq(a, b) (strcmp((a), (b)) == 0)

FILE* parse_arguments(int argc, char** argv)
{
	int i;
	int have_inst = 0;
	int have_data[3] = {};
	FILE* trace = NULL;
	int level;
	int num_blocks;
	int words_per_block;
	int associativity;
	char write_scheme;
	char alloc_scheme;
	char replace_scheme;
	int converted;

	for(i = 1; i < argc; i++)
	{
		if(streq(argv[i], "-I"))
		{
			if(i == (argc - 1))
				bad_params("Expected parameters after -I.");

			if(have_inst)
				bad_params("Duplicate I-cache parameters.");
			have_inst = 1;

			i++;
			converted = sscanf(argv[i], "%d:%d:%d:%c",
				&icache_info.num_blocks,
				&icache_info.words_per_block,
				&icache_info.associativity,
				&replace_scheme);

			if(converted < 4)
				bad_params("Invalid I-cache parameters.");

			if(icache_info.associativity > 1)
			{
				if(replace_scheme == 'R')
					icache_info.replacement = Replacement_RANDOM;
				else if(replace_scheme == 'L')
					icache_info.replacement = Replacement_LRU;
				else
					bad_params("Invalid I-cache replacement scheme.");
			}
		}
		else if(streq(argv[i], "-D"))
		{
			if(i == (argc - 1))
				bad_params("Expected parameters after -D.");

			i++;
			converted = sscanf(argv[i], "%d:%d:%d:%d:%c:%c:%c",
				&level, &num_blocks, &words_per_block, &associativity,
				&replace_scheme, &write_scheme, &alloc_scheme);

			if(converted < 7)
				bad_params("Invalid D-cache parameters.");

			if(level < 1 || level > 3)
				bad_params("Inalid D-cache level.");

			level--;
			if(have_data[level])
				bad_params("Duplicate D-cache level parameters.");

			have_data[level] = 1;

			dcache_info[level].num_blocks = num_blocks;
			dcache_info[level].words_per_block = words_per_block;
			dcache_info[level].associativity = associativity;

			if(associativity > 1)
			{
				if(replace_scheme == 'R')
					dcache_info[level].replacement = Replacement_RANDOM;
				else if(replace_scheme == 'L')
					dcache_info[level].replacement = Replacement_LRU;
				else
					bad_params("Invalid D-cache replacement scheme.");
			}

			if(write_scheme == 'B')
				dcache_info[level].write_scheme = Write_WRITE_BACK;
			else if(write_scheme == 'T')
				dcache_info[level].write_scheme = Write_WRITE_THROUGH;
			else
				bad_params("Invalid D-cache write scheme.");

			if(alloc_scheme == 'A')
				dcache_info[level].allocate_scheme = Allocate_ALLOCATE;
			else if(alloc_scheme == 'N')
				dcache_info[level].allocate_scheme = Allocate_NO_ALLOCATE;
			else
				bad_params("Invalid D-cache allocation scheme.");
		}
		else
		{
			if(i != (argc - 1))
				bad_params("Trace filename should be last argument.");

			break;
		}
	}

	if(!have_inst)
		bad_params("No I-cache parameters specified.");

	if(have_data[1] && !have_data[0])
		bad_params("L2 D-cache specified, but not L1.");

	if(have_data[2] && !have_data[1])
		bad_params("L3 D-cache specified, but not L2.");

	trace = fopen(argv[argc - 1], "r");

	if(trace == NULL)
		bad_params("Could not open trace file.");

	return trace;
}

int main(int argc, char** argv)
{
	FILE* trace = parse_arguments(argc, argv);

	setup_caches();

	while(!feof(trace))
		read_trace_line(trace);

	fclose(trace);

	print_statistics();
	return 0;
}