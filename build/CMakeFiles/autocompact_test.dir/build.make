# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.9

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local/bin/cmake

# The command to remove a file.
RM = /usr/local/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/meggie/文档/leveldb-multimem-dram

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/meggie/文档/leveldb-multimem-dram/build

# Include any dependencies generated for this target.
include CMakeFiles/autocompact_test.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/autocompact_test.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/autocompact_test.dir/flags.make

CMakeFiles/autocompact_test.dir/util/testharness.cc.o: CMakeFiles/autocompact_test.dir/flags.make
CMakeFiles/autocompact_test.dir/util/testharness.cc.o: ../util/testharness.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/meggie/文档/leveldb-multimem-dram/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/autocompact_test.dir/util/testharness.cc.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/autocompact_test.dir/util/testharness.cc.o -c /home/meggie/文档/leveldb-multimem-dram/util/testharness.cc

CMakeFiles/autocompact_test.dir/util/testharness.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/autocompact_test.dir/util/testharness.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/meggie/文档/leveldb-multimem-dram/util/testharness.cc > CMakeFiles/autocompact_test.dir/util/testharness.cc.i

CMakeFiles/autocompact_test.dir/util/testharness.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/autocompact_test.dir/util/testharness.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/meggie/文档/leveldb-multimem-dram/util/testharness.cc -o CMakeFiles/autocompact_test.dir/util/testharness.cc.s

CMakeFiles/autocompact_test.dir/util/testharness.cc.o.requires:

.PHONY : CMakeFiles/autocompact_test.dir/util/testharness.cc.o.requires

CMakeFiles/autocompact_test.dir/util/testharness.cc.o.provides: CMakeFiles/autocompact_test.dir/util/testharness.cc.o.requires
	$(MAKE) -f CMakeFiles/autocompact_test.dir/build.make CMakeFiles/autocompact_test.dir/util/testharness.cc.o.provides.build
.PHONY : CMakeFiles/autocompact_test.dir/util/testharness.cc.o.provides

CMakeFiles/autocompact_test.dir/util/testharness.cc.o.provides.build: CMakeFiles/autocompact_test.dir/util/testharness.cc.o


CMakeFiles/autocompact_test.dir/util/testutil.cc.o: CMakeFiles/autocompact_test.dir/flags.make
CMakeFiles/autocompact_test.dir/util/testutil.cc.o: ../util/testutil.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/meggie/文档/leveldb-multimem-dram/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object CMakeFiles/autocompact_test.dir/util/testutil.cc.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/autocompact_test.dir/util/testutil.cc.o -c /home/meggie/文档/leveldb-multimem-dram/util/testutil.cc

CMakeFiles/autocompact_test.dir/util/testutil.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/autocompact_test.dir/util/testutil.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/meggie/文档/leveldb-multimem-dram/util/testutil.cc > CMakeFiles/autocompact_test.dir/util/testutil.cc.i

CMakeFiles/autocompact_test.dir/util/testutil.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/autocompact_test.dir/util/testutil.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/meggie/文档/leveldb-multimem-dram/util/testutil.cc -o CMakeFiles/autocompact_test.dir/util/testutil.cc.s

CMakeFiles/autocompact_test.dir/util/testutil.cc.o.requires:

.PHONY : CMakeFiles/autocompact_test.dir/util/testutil.cc.o.requires

CMakeFiles/autocompact_test.dir/util/testutil.cc.o.provides: CMakeFiles/autocompact_test.dir/util/testutil.cc.o.requires
	$(MAKE) -f CMakeFiles/autocompact_test.dir/build.make CMakeFiles/autocompact_test.dir/util/testutil.cc.o.provides.build
.PHONY : CMakeFiles/autocompact_test.dir/util/testutil.cc.o.provides

CMakeFiles/autocompact_test.dir/util/testutil.cc.o.provides.build: CMakeFiles/autocompact_test.dir/util/testutil.cc.o


CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o: CMakeFiles/autocompact_test.dir/flags.make
CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o: ../db/autocompact_test.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/meggie/文档/leveldb-multimem-dram/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o -c /home/meggie/文档/leveldb-multimem-dram/db/autocompact_test.cc

CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/meggie/文档/leveldb-multimem-dram/db/autocompact_test.cc > CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.i

CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/meggie/文档/leveldb-multimem-dram/db/autocompact_test.cc -o CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.s

CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.requires:

.PHONY : CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.requires

CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.provides: CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.requires
	$(MAKE) -f CMakeFiles/autocompact_test.dir/build.make CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.provides.build
.PHONY : CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.provides

CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.provides.build: CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o


# Object files for target autocompact_test
autocompact_test_OBJECTS = \
"CMakeFiles/autocompact_test.dir/util/testharness.cc.o" \
"CMakeFiles/autocompact_test.dir/util/testutil.cc.o" \
"CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o"

# External object files for target autocompact_test
autocompact_test_EXTERNAL_OBJECTS =

autocompact_test: CMakeFiles/autocompact_test.dir/util/testharness.cc.o
autocompact_test: CMakeFiles/autocompact_test.dir/util/testutil.cc.o
autocompact_test: CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o
autocompact_test: CMakeFiles/autocompact_test.dir/build.make
autocompact_test: libleveldb.a
autocompact_test: CMakeFiles/autocompact_test.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/meggie/文档/leveldb-multimem-dram/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Linking CXX executable autocompact_test"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/autocompact_test.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/autocompact_test.dir/build: autocompact_test

.PHONY : CMakeFiles/autocompact_test.dir/build

CMakeFiles/autocompact_test.dir/requires: CMakeFiles/autocompact_test.dir/util/testharness.cc.o.requires
CMakeFiles/autocompact_test.dir/requires: CMakeFiles/autocompact_test.dir/util/testutil.cc.o.requires
CMakeFiles/autocompact_test.dir/requires: CMakeFiles/autocompact_test.dir/db/autocompact_test.cc.o.requires

.PHONY : CMakeFiles/autocompact_test.dir/requires

CMakeFiles/autocompact_test.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/autocompact_test.dir/cmake_clean.cmake
.PHONY : CMakeFiles/autocompact_test.dir/clean

CMakeFiles/autocompact_test.dir/depend:
	cd /home/meggie/文档/leveldb-multimem-dram/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/meggie/文档/leveldb-multimem-dram /home/meggie/文档/leveldb-multimem-dram /home/meggie/文档/leveldb-multimem-dram/build /home/meggie/文档/leveldb-multimem-dram/build /home/meggie/文档/leveldb-multimem-dram/build/CMakeFiles/autocompact_test.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/autocompact_test.dir/depend

