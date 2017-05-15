from hashlib import blake2s, sha256

from ReferenceMerkleSet import *

__all__ = ['confirm_included', 'confirm_included_already_hashed', 'confirm_not_included', 
        'confirm_not_included_already_hashed', 'MerkleSet']

"""
The behavior of this implementation is semantically identical to the one in ReferenceMerkleSet

Advantages of this merkle tree implementation:
Lazy root calculation
Few l1 and l2 cache misses
Good memory efficiency
Reasonable defense against malicious insertion attacks

TODO: Port to C
TODO: Optimize! Benchmark!
TODO: Make sure that data structures don't get garbled on an out of memory error
TODO: add multi-threading support
TODO: add support for continuous self-auditing
TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
TODO: Try unrolling all this recursivity to improve performance
TODO: Maybe add a size counter
TODO: Add combining of multiproofs and looking up a whole multiproof at once

Branch memory allocation data format:

# The active child is the leaf where overflow is currently sent to
# When the active child is filled, a new empty one is made
# When a leaf overflows, the data is sent to the active child of the parent branch
# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: modified_hash 32 modified_hash 32 patricia[n-1] patricia[n-1]
# unused are zeroed out. If child is a branch pos is set to 0xFFFF
patricia[0]: child 8 pos 2
# modified_hash[0] & 0xC0 is the type
type: EMPTY or TERMINAL or MIDDLE or INVALID

Leaf memory allocation data format:

# first_unused is the start of linked list, 0xFFFF for terminal
# num_inputs is the number of references from the parent branch into this leaf
leaf: first_unused 2 num_inputs 2 [node or emptynode]
# pos0 and pos1 are one based indexes to make it easy to detect if they are accidently cleared to zero
node: modified_hash 32 modified_hash 32 pos0 2 pos1 2
# next is a zero based index
emptynode: next 2 unused 66
"""

# Returned in branch updates when the terminal was unused
NOTSTARTED = 2
# Returned in removal when there's only one left
ONELEFT = 3
# Fragile is returned when there might be only two things below
# Bubbles upwards as long as there's an empty sibling
# When a non-empty sibling is hit, it calls catch on the layer below
# On catch, collapse is called on everything below
# Collapse returns None if it has more than two things, or both if both terminal
# If there is an empty child, collapse passes through the return of its non-empty child
# Collapse clears out if it's returning something other than None
FRAGILE = 4
INVALIDATING = 5
DONE = 6
FULL = 7

HASHSIZE = 32
SHORTSIZE = 2
        
def from_bytes(f):
    return int.from_bytes(f, 'big')

def to_bytes(f, v):
    return int.to_bytes(f, v, 'big')

# Sanity checking on top of the hash function
def hashaudit(mystr):
    assert len(mystr) == 64
    t0, t1 = get_type(mystr, 0), get_type(mystr, 32)
    assert t0 != INVALID and t1 != INVALID
    if (t0 == EMPTY or t0 == TERMINAL) and (t1 == EMPTY or t1 == TERMINAL):
        assert t0 == TERMINAL and t1 == TERMINAL
        assert mystr[:32] < mystr[32:]
    assert t0 != EMPTY or mystr[:32] == BLANK
    assert t1 != EMPTY or mystr[32:] == BLANK
    return hashdown(mystr)

def get_type(mybytes, pos):
    return mybytes[pos] & INVALID

def make_invalid(mybytes, pos):
    assert get_type(mybytes, pos) != INVALID
    mybytes[pos] |= INVALID

# Bounds checking for the win
class safearray(bytearray):
    def __setitem__(self, index, thing):
        if type(index) is slice:
            start = index.start
            if start is None:
                start = 0
            stop = index.stop
            if stop is None:
                stop = len(self)
            assert index.step is None
            assert start >= 0
            assert stop >= 0
            assert start < len(self)
            assert stop <= len(self)
            assert stop - start == len(thing)
        else:
            assert index >= 0
            assert index < len(self)
        bytearray.__setitem__(self, index, thing)

class Node:
    def __init__(self,data,pos):
        self.data = data
        self.pos = pos

    def get_offset(self):
        return self.pos

    def make_unused(self,nextent):
        self.data[self.pos:self.pos + 2] = to_bytes(nextent,2)
        self.data[self.pos + 2:self.pos + 68] = bytes(66)

    def get_unused_ptr(self):
        assert self.data[self.pos+2:self.pos+68] == bytes(66) and from_bytes(self.data[self.pos:self.pos+2]) != 0
        return from_bytes(self.data[self.pos:self.pos+2])
        
    def hash_loc(self,n):
        return self.pos + (n * HASHSIZE)

    def pos_loc(self,n):
        return self.pos + 64 + (n * SHORTSIZE)

    def get_hash(self,n):
        offset = self.hash_loc(n)
        return self.data[offset:offset+HASHSIZE]

    def set_hash(self,n,v):
        offset = self.hash_loc(n)
        self.data[offset:offset+HASHSIZE] = v

    def get_pos(self,n):
        offset = self.pos_loc(n)
        res = from_bytes(self.data[offset:offset+SHORTSIZE])
        if res != 0xffff:
            return res - 1
        else:
            return res

    def set_pos(self,n,v):
        offset = self.pos_loc(n)
        if v != 0xffff:
            v += 1
        self.data[offset:offset+SHORTSIZE] = to_bytes(v, 2)

    def get_type(self,n):
        offset = self.hash_loc(n)
        return get_type(self.data, offset)
    
    def make_invalid(self,n):
        offset = self.hash_loc(n)
        return make_invalid(self.data, offset)

class Leaf(safearray):
    def get_next_ptr(self):
        return from_bytes(self[:2])

    def set_next_ptr(self,ptr):
        self[:2] = to_bytes(ptr, 2)

    def get_node(self,pos):
        assert pos >= 0 and (4 + 68 * (pos + 1)) <= len(self)
        return Node(self, 4 + 68 * pos)

    def get_inputs(self):
        return from_bytes(self[2:4])

    def set_inputs(self,i):
        self[2:4] = to_bytes(i, 2)        
        
class MerkleSet:
    # depth sets the size of branches, it's power of two scale with a smallest value of 0
    # leaf_units is the size of leaves, its smallest possible value is 1
    # Optimal values for both of those are heavily dependent on the memory architecture of 
    # the particular machine
    def __init__(self, depth, leaf_units):
        self.subblock_lengths = [10]
        while len(self.subblock_lengths) <= depth:
            self.subblock_lengths.append(64 + 2 * self.subblock_lengths[-1])
        self.leaf_units = leaf_units
        self.root = bytearray(32)
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.rootblock = None

    # Only used by test code, makes sure internal state is consistent
    def audit(self, hashes):
        newhashes = []
        t = get_type(self.root, 0)
        if t == EMPTY:
            assert self.root == BLANK
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
        elif t == TERMINAL:
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
            newhashes.append(self.root)
        else:
            allblocks = set()
            e = (self.root if t == MIDDLE else None)
            self._audit_branch(self._addrof(self.rootblock), 0, allblocks, e, newhashes, True)
            assert allblocks == set(self.pointers_to_arrays.keys())
        s = sorted([set_terminal(x) for x in hashes])
        assert newhashes == s

    def _audit_branch(self, branch, depth, allblocks, expected, hashes, can_terminate):
        assert branch not in allblocks
        allblocks.add(branch)
        outputs = {}
        branch = self._deref(branch)
        assert len(branch) == 8 + self.subblock_lengths[-1]
        self._audit_branch_inner(branch, 8, depth, len(self.subblock_lengths) - 1, outputs, allblocks, expected, hashes, can_terminate)
        active = branch[:8]
        if active != bytes(8):
            assert bytes(active) in outputs
        for leaf, positions in outputs.items():
            assert leaf not in allblocks
            allblocks.add(leaf)
            self._audit_whole_leaf(leaf, positions)

    def _audit_branch_inner(self, branch, pos, depth, moddepth, outputs, allblocks, expected, hashes, can_terminate):
        if moddepth == 0:
            newpos = from_bytes(branch[pos + 8:pos + 10])
            output = bytes(branch[pos:pos + 8])
            assert bytes(output) in self.pointers_to_arrays
            if newpos == 0xFFFF:
                self._audit_branch(output, depth, allblocks, expected, hashes, can_terminate)
            else:
                outputs.setdefault(output, []).append((newpos, expected))
                self._add_hashes_leaf(self._deref(output), newpos, hashes, can_terminate)
            return
        t0 = get_type(branch, pos)
        t1 = get_type(branch, pos + 32)
        if expected is not None:
            assert t0 != INVALID and t1 != INVALID and hashaudit(branch[pos:pos + 64]) == expected
        if t0 == EMPTY:
            assert t1 != EMPTY and t1 != TERMINAL
            assert branch[pos:pos + 32] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        elif t0 == TERMINAL:
            assert can_terminate or t1 != TERMINAL
            assert t1 != EMPTY
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
            hashes.append(branch[pos:pos + 32])
        else:
            e = (branch[pos:pos + 32] if t0 == MIDDLE else None)
            self._audit_branch_inner(branch, pos + 64, depth + 1, moddepth - 1, outputs, allblocks, e, hashes, t1 != EMPTY)
        if t1 == EMPTY:
            assert branch[pos + 32:pos + 64] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        elif t1 == TERMINAL:
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            hashes.append(branch[pos + 32:pos + 64])
        else:
            e = (branch[pos + 32:pos + 64] if t1 == MIDDLE else None)
            self._audit_branch_inner(branch, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, outputs, allblocks, e, hashes, t0 != EMPTY)

    def _add_hashes_leaf(self, leaf, pos, hashes, can_terminate):
        node = leaf.get_node(pos)
        t0 = node.get_type(0)
        t1 = node.get_type(1)
        if t0 == TERMINAL:
            hashes.append(node.get_hash(0))
            assert can_terminate or t1 != TERMINAL
        elif t0 != EMPTY:
            self._add_hashes_leaf(leaf, node.get_pos(0), hashes, t1 != EMPTY)
        if t1 == TERMINAL:
            hashes.append(node.get_hash(1))
        elif t1 != EMPTY:
            self._add_hashes_leaf(leaf, node.get_pos(1), hashes, t0 != EMPTY)

    def _audit_branch_inner_empty(self, branch, pos, moddepth):
        if moddepth == 0:
            assert branch[pos:pos + 10] == bytes(10)
            return
        assert branch[pos:pos + 64] == bytes(64)
        self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)

    def _audit_whole_leaf(self, leaf, inputs):
        leaf = self._deref(leaf)
        assert len(leaf) == 4 + self.leaf_units * 68
        assert len(inputs) == leaf.get_inputs()
        # 88 is the ASCII value for 'X'
        mycopy = bytearray([88] * (4 + self.leaf_units * 68))
        for pos, expected in inputs:
            self._audit_whole_leaf_inner(leaf, mycopy, pos, expected)
        i = leaf.get_next_ptr()
        while i != 0xFFFF:
            nexti = from_bytes(leaf[4 + i * 68:4 + i * 68 + 2])
            assert mycopy[4 + i * 68:4 + i * 68 + 68] == b'X' * 68
            mycopy[4 + i * 68:4 + i * 68 + 68] = bytes(68)
            mycopy[4 + i * 68:4 + i * 68 + 2] = to_bytes(nexti, 2)
            i = nexti
        assert mycopy[4:] == leaf[4:]

    def _audit_whole_leaf_inner(self, leaf, mycopy, pos, expected):
        assert pos >= 0
        rpos = 4 + pos * 68
        assert mycopy[rpos:rpos + 68] == b'X' * 68
        mycopy[rpos:rpos + 68] = leaf[rpos:rpos + 68]

        source_node = Node(leaf,rpos)

        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)

        if expected is not None:
            assert t0 != INVALID and t1 != INVALID and hashaudit(source_node.get_hash(0) + source_node.get_hash(1)) == expected
        if t0 == EMPTY:
            assert t1 != EMPTY
            assert t1 != TERMINAL
            assert source_node.get_hash(0) == BLANK
            assert source_node.get_pos(0) == -1
        elif t0 == TERMINAL:
            assert t1 != EMPTY
            assert source_node.get_pos(0) == -1
        else:
            e = (source_node.get_hash(0) if t0 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, source_node.get_pos(0), e)
        if t1 == EMPTY:
            assert source_node.get_hash(1) == BLANK
            assert source_node.get_pos(1) == -1
        elif t1 == TERMINAL:
            assert source_node.get_pos(1) == -1
        else:
            e = (source_node.get_hash(1) if t1 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, source_node.get_pos(1), e)

    # In C this should be malloc/new
    def _allocate_branch(self):
        b = safearray(8 + self.subblock_lengths[-1])
        self.pointers_to_arrays[self._addrof(b, False)] = b
        return b

    # In C this should be malloc/new
    def _allocate_leaf(self):
        leaf = Leaf(4 + self.leaf_units * 68)
        for i in range(self.leaf_units):
            p = 4 + i * 68
            leaf[p:p + 2] = to_bytes((i + 1) if i != self.leaf_units - 1 else 0xFFFF, 2)
        self.pointers_to_arrays[self._addrof(leaf, False)] = leaf
        return leaf

    # In C this should be calloc/free
    def _deallocate(self, thing):
        del self.pointers_to_arrays[self._addrof(thing)]

    # In C this should be *
    def _deref(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[bytes(ref)]

    # In C this should be &
    def _addrof(self, thing, check=True):
        assert thing is not None
        assert not check or any(x == thing for x in self.pointers_to_arrays.values())
        return to_bytes(id(thing), 8)

    def get_root(self):
        if get_type(self.root, 0) == INVALID:
            self.root[0:] = self._force_calculation_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
        return bytes(self.root)

    def _force_calculation_branch(self, block, pos, moddepth):
        if moddepth == 0:
            block2 = self._deref(block[pos:pos + 8])
            pos = from_bytes(block[pos + 8:pos + 10])
            if pos == 0xFFFF:
                return self._force_calculation_branch(block2, 8, len(self.subblock_lengths) - 1)
            else:
                return self._force_calculation_leaf(block2, pos)
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_branch(block, pos + 64, moddepth - 1)
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        return hashaudit(block[pos:pos + 64])

    def _force_calculation_leaf(self, block, pos):
        pos = 4 + pos * 68
        node = Node(block, pos)
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_leaf(block, node.get_pos(0))
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_leaf(block, node.get_pos(1))
        return hashaudit(block[pos:pos + 64])

    # Convenience function
    def add(self, toadd):
        return self.add_already_hashed(sha256(toadd).digest())

    def add_already_hashed(self, toadd):
        self._add(set_terminal(toadd))

    def _add(self, toadd):
        t = get_type(self.root, 0)
        if t == EMPTY:
            self.root[0:] = toadd
        elif t == TERMINAL:
            if toadd == self.root:
                return
            self.rootblock = self._allocate_branch()
            self._insert_branch([self.root, toadd], self.rootblock, 8, 0, len(self.subblock_lengths) - 1)
            make_invalid(self.root, 0)
        else:
            if self._add_to_branch(toadd, self.rootblock, 0) == INVALIDATING and get_type(self.root, 0) != INVALID:
                make_invalid(self.root, 0)

    # returns INVALIDATING, DONE
    def _add_to_branch(self, toadd, block, depth):
        return self._add_to_branch_inner(toadd, block, 8, depth, len(self.subblock_lengths) - 1)

    # returns NOTSTARTED, INVALIDATING, DONE
    def _add_to_branch_inner(self, toadd, block, pos, depth, moddepth):
        if moddepth == 0:
            nextblock = self._deref(block[pos:pos + 8])
            if nextblock is None:
                return NOTSTARTED
            nextpos = from_bytes(block[pos + 8:pos + 10])
            if nextpos == 0xFFFF:
                return self._add_to_branch(toadd, nextblock, depth)
            else:
                return self._add_to_leaf(toadd, block, pos, nextblock, nextpos, depth)
        if get_bit(toadd, depth) == 0:
            r = self._add_to_branch_inner(toadd, block, pos + 64, depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos) != INVALID:
                    make_invalid(block, pos)
                    if get_type(block, pos + 32) != INVALID:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = get_type(block, pos)
            t1 = get_type(block, pos + 32)
            if t0 == EMPTY:
                if t1 == EMPTY:
                    return NOTSTARTED
                block[pos:pos + 32] = toadd
                if t1 != INVALID:
                    return INVALIDATING
                else:
                    return DONE
            assert t0 == TERMINAL
            v0 = block[pos:pos + 32]
            if v0 == toadd:
                return DONE
            if t1 == TERMINAL:
                v1 = block[pos + 32:pos + 64]
                if v1 == toadd:
                    return DONE
                block[pos + 32:pos + 64] = bytes(32)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v0], block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            if t1 != INVALID:
                return INVALIDATING
            else:
                return DONE
        else:
            r = self._add_to_branch_inner(toadd, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos + 32) != INVALID:
                    make_invalid(block, pos + 32)
                    if get_type(block, pos) != INVALID:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = get_type(block, pos)
            t1 = get_type(block, pos + 32)
            if t1 == EMPTY:
                if t0 == EMPTY:
                    return NOTSTARTED
                block[pos + 32:pos + 64] = toadd
                if t0 != INVALID:
                    return INVALIDATING
                else:
                    return DONE
            assert t1 == TERMINAL
            v1 = block[pos + 32:pos + 64]
            if v1 == toadd:
                return DONE
            if t0 == TERMINAL:
                v0 = block[pos:pos + 32]
                if v0 == toadd:
                    return DONE
                block[pos:pos + 32] = bytes(32)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v1], block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)
            if t0 != INVALID:
                return INVALIDATING
            else:
                return DONE

    def _insert_branch(self, things, block, pos, depth, moddepth):
        assert 2 <= len(things) <= 3
        if moddepth == 0:
            child = self._deref(block[:8])
            r = FULL
            if child is not None:
                r, leafpos = self._insert_leaf(things, child, depth)
            if r == FULL:
                child = self._allocate_leaf()
                r, leafpos = self._insert_leaf(things, child, depth)
                if r == FULL:
                    self._deallocate(child)
                    newb = self._allocate_branch()
                    block[pos:pos + 8] = self._addrof(newb)
                    block[pos + 8:pos + 10] = to_bytes(0xFFFF, 2)
                    self._insert_branch(things, newb, 8, depth, len(self.subblock_lengths) - 1)
                    return
                block[:8] = self._addrof(child)
            # increment the number of inputs in the active child
            child.set_inputs(child.get_inputs() + 1)
            block[pos:pos + 8] = self._addrof(child)
            block[pos + 8:pos + 10] = to_bytes(leafpos, 2)
            return
        things.sort()
        if len(things) == 2:
            block[pos:pos + 32] = things[0]
            block[pos + 32:pos + 64] = things[1]
            return
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            if bits[0] == 0:
                self._insert_branch(things, block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            else:
                self._insert_branch(things, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)
        else:
            if bits[0] == bits[1]:
                block[pos + 32:pos + 64] = things[2]
                self._insert_branch(things[:2], block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            else:
                block[pos:pos + 32] = things[0]
                self._insert_branch(things[1:], block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)

    # returns INVALIDATING, DONE
    def _add_to_leaf(self, toadd, branch, branchpos, leaf, leafpos, depth):
        r = self._add_to_leaf_inner(toadd, leaf, leafpos, depth)
        if r != FULL:
            return r
        if leaf.get_inputs() == 1:
            # leaf is full and only has one input
            # it cannot be split so it must be replaced with a branch
            newb = self._allocate_branch()
            self._copy_leaf_to_branch(newb, 8, len(self.subblock_lengths) - 1, leaf, leafpos)
            self._add_to_branch(toadd, newb, depth)
            branch[branchpos:branchpos + 8] = self._addrof(newb)
            branch[branchpos + 8:branchpos + 10] = to_bytes(0xFFFF, 2)
            if branch[:8] == self._addrof(leaf):
                branch[:8] = bytes(8)
            self._deallocate(leaf)
            return INVALIDATING
        active = self._deref(branch[:8])
        if active is None or active is leaf:
            active = self._allocate_leaf()
        r, newpos = self._copy_between_leafs(leaf, active, leafpos)
        if r != DONE:
            active = self._allocate_leaf()
            r, newpos = self._copy_between_leafs(leaf, active, leafpos)
            assert r == DONE
        branch[branchpos:branchpos + 8] = self._addrof(active)
        if branch[:8] != self._addrof(active):
            branch[:8] = self._addrof(active)
        branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
        self._delete_from_leaf(leaf, leafpos)
        return self._add_to_leaf(toadd, branch, branchpos, active, newpos, depth)

    # returns INVALIDATING, DONE, FULL
    def _add_to_leaf_inner(self, toadd, leaf, pos, depth):
        assert pos >= 0
        node = leaf.get_node(pos)
        if get_bit(toadd, depth) == 0:
            t = node.get_type(0)
            if t == EMPTY:
                node.set_hash(0, toadd)
                return INVALIDATING
            elif t == TERMINAL:
                oldval0 = node.get_hash(0)
                if oldval0 == toadd:
                    return DONE
                t1 = node.get_type(1)
                if t1 == TERMINAL:
                    oldval1 = node.get_hash(1)
                    if toadd == oldval1:
                        return DONE
                    nextpos = leaf.get_next_ptr()
                    leaf.set_next_ptr(pos)
                    node.make_unused(nextpos)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf.set_next_ptr(nextpos)
                        node.set_hash(0, oldval0)
                        node.set_hash(1, oldval1)
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval0], leaf, depth + 1)
                if r == FULL:
                    return FULL
                node.set_pos(0, newpos)
                node.make_invalid(0)
                if node.get_type(1) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, node.get_pos(0), depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        node.make_invalid(0)
                        return INVALIDATING
                    return DONE
                return r
        else:
            t = node.get_type(1)
            if t == EMPTY:
                node.set_hash(1, toadd)
                return INVALIDATING
            elif t == TERMINAL:
                oldval1 = node.get_hash(1)
                if oldval1 == toadd:
                    return DONE
                t0 = node.get_type(0)
                if t0 == TERMINAL:
                    oldval0 = node.get_hash(0)
                    if toadd == oldval0:
                        return DONE
                    nextpos = leaf.get_next_ptr()
                    leaf.set_next_ptr(pos)
                    node.make_unused(nextpos)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf.set_next_ptr(nextpos)
                        node.set_hash(0, oldval0)
                        node.set_hash(1, oldval1)
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval1], leaf, depth + 1)
                if r == FULL:
                    return FULL
                node.set_pos(1, newpos)
                node.make_invalid(1)
                if node.get_type(0) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, node.get_pos(1), depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        node.make_invalid(1)
                        return INVALIDATING
                    return DONE
                return r

    # returns state, newpos
    # state can be FULL, DONE
    def _copy_between_leafs(self, fromleaf, toleaf, frompos):
        r, pos = self._copy_between_leafs_inner(fromleaf, toleaf, frompos)
        if r == DONE:
            toleaf.set_inputs(toleaf.get_inputs() + 1)
            fromleaf.set_inputs(fromleaf.get_inputs() - 1)
        return r, pos

    # returns state, newpos
    # state can be FULL, DONE
    def _copy_between_leafs_inner(self, fromleaf, toleaf, frompos):
        topos = toleaf.get_next_ptr()
        if topos == 0xFFFF:
            return FULL, None
        from_node = fromleaf.get_node(frompos)
        to_node = toleaf.get_node(topos)
        toleaf.set_next_ptr(to_node.get_unused_ptr())
        t0 = from_node.get_type(0)
        lowpos = None
        highpos = None
        if t0 == MIDDLE or t0 == INVALID:
            r, lowpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_node.get_pos(0))
            if r == FULL:
                assert toleaf.get_next_ptr() == to_node.get_unused_ptr()
                toleaf.set_next_ptr(topos)
                return FULL, None
        t1 = from_node.get_type(1)
        if t1 == MIDDLE or t1 == INVALID:
            r, highpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_node.get_pos(1))
            if r == FULL:
                if t0 == MIDDLE or t0 == INVALID:
                    self._delete_from_leaf(toleaf, lowpos)
                assert toleaf.get_next_ptr() == to_node.get_unused_ptr()
                toleaf.set_next_ptr(topos)
                return FULL, None
        to_node.set_hash(0, from_node.get_hash(0))
        to_node.set_hash(1, from_node.get_hash(1))
        if lowpos is not None:
            to_node.set_pos(0, lowpos)
        if highpos is not None:
            to_node.set_pos(1, highpos)
        return DONE, topos

    def _delete_from_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        node = Node(leaf, rpos)
        t = get_type(leaf, rpos)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, node.get_pos(0))
        t = get_type(leaf, rpos + 32)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, node.get_pos(1))
        node.make_unused(leaf.get_next_ptr())
        leaf.set_next_ptr(pos)

    def _copy_leaf_to_branch(self, branch, branchpos, moddepth, leaf, leafpos):
        assert leafpos >= 0
        node = leaf.get_node(leafpos)
        if moddepth == 0:
            active = self._deref(branch[:8])
            if active is None:
                active = self._allocate_leaf()
                branch[0:8] = self._addrof(active)
            r, newpos = self._copy_between_leafs_inner(leaf, active, leafpos)
            assert r == DONE
            active.set_inputs(active.get_inputs() + 1)
            branch[branchpos:branchpos + 8] = self._addrof(active)
            branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
            return
        branch[branchpos:branchpos + 64] = node.get_hash(0) + node.get_hash(1)
        t = node.get_type(0)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64, moddepth - 1, leaf, node.get_pos(0))
        t = node.get_type(1)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1, leaf, node.get_pos(1))

    # returns (status, pos)
    # status can be INVALIDATING, FULL
    def _insert_leaf(self, things, leaf, depth):
        assert 2 <= len(things) <= 3
        for thing in things:
            assert len(thing) == 32
        pos = from_bytes(leaf[:2])
        if pos == 0xFFFF:
            return FULL, None
        lpos = pos * 68 + 4
        leaf[:2] = leaf[lpos:lpos + 2]
        things.sort()
        if len(things) == 2:
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 32:lpos + 64] = things[1]
            return INVALIDATING, pos
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            r, laterpos = self._insert_leaf(things, leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            if bits[0] == 0:
                leaf[lpos + 64:lpos + 66] = to_bytes(laterpos + 1, 2)
                make_invalid(leaf, lpos)
            else:
                leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
                make_invalid(leaf, lpos + 32)
                leaf[lpos:lpos + 2] = bytes(2)
            return INVALIDATING, pos
        elif bits[0] == bits[1]:
            r, laterpos = self._insert_leaf([things[0], things[1]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos + 32:lpos + 64] = things[2]
            leaf[lpos + 64:lpos + 66] = to_bytes(laterpos + 1, 2)
            make_invalid(leaf, lpos)
        else:
            r, laterpos = self._insert_leaf([things[1], things[2]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
            make_invalid(leaf, lpos + 32)
        return INVALIDATING, pos

    # Convenience function
    def remove(self, toremove):
        return self.remove_already_hashed(sha256(toremove).digest())

    def remove_already_hashed(self, toremove):
        return self._remove(set_terminal(toremove))

    def _remove(self, toremove):
        t = get_type(self.root, 0)
        if t == EMPTY:
            return
        elif t == TERMINAL:
            if toremove == self.root:
                self.root[0:] = BLANK
            return
        else:
            status, oneval = self._remove_branch(toremove, self.rootblock, 0)
        if status == INVALIDATING:
            make_invalid(self.root, 0)
        elif status == ONELEFT:
            self.root[0:] = oneval
            self.rootblock = None
        elif status == FRAGILE:
            self._catch_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
            if get_type(self.root, 0) != INVALID:
                make_invalid(self.root, 0)

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_branch(self, toremove, block, depth):
        result, val = self._remove_branch_inner(toremove, block, 8, depth, len(self.subblock_lengths) - 1)
        assert result != NOTSTARTED
        if result == ONELEFT:
            self._deallocate(block)
        return result, val

    # returns (status, oneval)
    # status can be NOTSTARTED, ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_branch_inner(self, toremove, block, pos, depth, moddepth):
        if moddepth == 0:
            if block[pos:pos + 8] == bytes(8):
                return NOTSTARTED, None
            p = from_bytes(block[pos + 8:pos + 10])
            if p == 0xFFFF:
                r, val = self._remove_branch(toremove, self._deref(block[pos:pos + 8]), depth)
            else:
                r, val = self._remove_leaf(toremove, self._deref(block[pos:pos + 8]), p, depth, block)
            if r == ONELEFT:
                block[pos:pos + 10] = bytes(10)
            return r, val
        if get_bit(toremove, depth) == 0:
            r, val = self._remove_branch_inner(toremove, block, pos + 64, depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = get_type(block, pos)
                if t == EMPTY:
                    if get_type(block, pos + 32) == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos:pos + 32] == toremove:
                    t1 = get_type(block, pos + 32)
                    if t1 == TERMINAL:
                        left = block[pos + 32:pos + 64]
                        block[pos:pos + 64] = bytes(64)
                        return ONELEFT, left
                    else:
                        assert t1 != EMPTY
                        block[pos:pos + 32] = bytes(32)
                        return FRAGILE, None
                elif block[pos + 32:pos + 64] == toremove:
                    left = block[pos:pos + 32]
                    block[pos:pos + 64] = bytes(64)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = get_type(block, pos) == INVALID
                block[pos:pos + 32] = val
                if get_type(block, pos + 32) == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                else:
                    return DONE, None
            elif r == FRAGILE:
                t1 = get_type(block, pos + 32)
                # scan up the tree until the other child is non-empty
                if t1 == EMPTY:
                    if get_type(block, pos) != INVALID:
                        make_invalid(block, pos)
                    return FRAGILE, None
                # the other child is non-empty, if the tree can be collapsed
                # it will be up to the level below this one, so try that
                self._catch_branch(block, pos + 64, moddepth - 1)
                # done collasping, continue invalidating if neccessary
                if get_type(block, pos) == INVALID:
                    return DONE, None
                make_invalid(block, pos)
                if t1 == INVALID:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = get_type(block, pos)
                if t == INVALID:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    make_invalid(block, pos)
                    if get_type(block, pos + 32) == INVALID:
                        return DONE, None
                    return INVALIDATING, None
            assert r == DONE
            return r, val
        else:
            r, val = self._remove_branch_inner(toremove, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = get_type(block, pos + 32)
                if t == EMPTY:
                    if get_type(block, pos) == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos + 32:pos + 64] == toremove:
                    if get_type(block, pos) == TERMINAL:
                        left = block[pos:pos + 32]
                        block[pos:pos + 64] = bytes(64)
                        return ONELEFT, left
                    else:
                        block[pos + 32:pos + 64] = bytes(32)
                        return FRAGILE, None
                elif block[pos:pos + 32] == toremove:
                    left = block[pos + 32:pos + 64]
                    block[pos:pos + 64] = bytes(64)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = get_type(block, pos + 32) == INVALID
                block[pos + 32:pos + 64] = val
                if get_type(block, pos) == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                return DONE, None
            elif r == FRAGILE:
                t0 = get_type(block, pos)
                if t0 == EMPTY:
                    if get_type(block, pos + 32) != INVALID:
                        make_invalid(block, pos + 32)
                    return FRAGILE, None
                self._catch_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                if get_type(block, pos + 32) == INVALID:
                    return DONE, None
                make_invalid(block, pos + 32)
                if t0 == INVALID:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = get_type(block, pos + 32)
                if t == INVALID:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    make_invalid(block, pos + 32)
                    if get_type(block, pos) == INVALID:
                        return DONE, None
                    return INVALIDATING, None
            assert r == DONE
            return r, val

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf(self, toremove, block, pos, depth, branch):
        result, val = self._remove_leaf_inner(toremove, block, pos, depth)
        if result == ONELEFT:
            numin = block.get_inputs()
            if numin == 1:
                if branch[:8] == self._addrof(block):
                    branch[:8] = bytes(8)
                self._deallocate(block)
            else:
                block.set_inputs(numin - 1)
        return result, val

    def _deallocate_leaf_node(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        node = Node(leaf, rpos)
        next_entry = leaf.get_next_ptr()
        target_node = Node(leaf, rpos)
        target_node.make_unused(next_entry)
        leaf.set_next_ptr(pos)

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf_inner(self, toremove, block, pos, depth):
        assert pos >= 0
        rpos = 4 + pos * 68
        node = Node(block, rpos)
        if get_bit(toremove, depth) == 0:
            t = get_type(block, rpos)
            if t == EMPTY:
                return DONE, None
            if t == TERMINAL:
                t1 = get_type(block, rpos + 32)
                if node.get_hash(0) == toremove:
                    if t1 == TERMINAL:
                        left = node.get_hash(1)
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    node.set_hash(0, bytes(32))
                    return FRAGILE, None
                if node.get_hash(1) == toremove:
                    left = node.get_hash(0)
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 64:rpos + 66]) - 1, depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(block, rpos)
                        if get_type(block, rpos + 32) != INVALID:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t1 = get_type(block, rpos + 32)
                    assert t1 != EMPTY
                    node.set_hash(0, val)
                    node.set_pos(0, -1)
                    if t1 == TERMINAL:
                        return FRAGILE, None
                    if t != INVALID and t1 != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t1 = get_type(block, rpos + 32)
                if t1 == EMPTY:
                    if t != INVALID:
                        make_invalid(block, rpos)
                    return FRAGILE, None
                self._catch_leaf(block, node.get_pos(0))
                if t == INVALID:
                    return DONE, None
                make_invalid(block, rpos)
                if t1 == INVALID:
                    return DONE, None
                return INVALIDATING, None
        else:
            t = get_type(block, rpos + 32)
            if t == EMPTY:
                return DONE, None
            elif t == TERMINAL:
                t0 = get_type(block, rpos)
                if node.get_hash(1) == toremove:
                    if t0 == TERMINAL:
                        left = node.get_hash(0)
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    node.set_hash(1, bytes(32))
                    return FRAGILE, None
                if node.get_hash(0) == toremove:
                    left = node.get_hash(1)
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, node.get_pos(1), depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(block, rpos + 32)
                        if get_type(block, rpos) != INVALID:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t0 = get_type(block, rpos)
                    assert t0 != EMPTY
                    node.set_hash(1, val)
                    node.set_pos(1, -1)
                    if t0 == TERMINAL:
                        return FRAGILE, None
                    if t != INVALID and t0 != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t0 = get_type(block, rpos)
                if t0 == EMPTY:
                    if t != INVALID:
                        make_invalid(block, rpos + 32)
                    return FRAGILE, None
                self._catch_leaf(block, node.get_pos(1))
                if get_type(block, rpos + 32) == INVALID:
                    return DONE, None
                make_invalid(block, rpos + 32)
                if t0 == INVALID:
                    return DONE, None
                return INVALIDATING, None

    def _catch_branch(self, block, pos, moddepth):
        if moddepth == 0:
            leafpos = from_bytes(block[pos + 8:pos + 10])
            if leafpos == 0xFFFF:
                self._catch_branch(self._deref(block[pos:pos + 8]), 8, len(self.subblock_lengths) - 1)
            else:
                self._catch_leaf(self._deref(block[pos:pos + 8]), leafpos)
            return
        if get_type(block, pos) == EMPTY:
            assert get_type(block, pos + 32) != TERMINAL
            r = self._collapse_branch_inner(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos:pos + 64] = r
            return
        if get_type(block, pos + 32) == EMPTY:
            assert get_type(block, pos) != TERMINAL
            r = self._collapse_branch_inner(block, pos + 64, moddepth - 1)
            if r != None:
                block[pos:pos + 64] = r

    # returns two hashes string or None
    def _collapse_branch(self, block):
        r = self._collapse_branch_inner(block, 8, len(self.subblock_lengths) - 1)
        if r != None:
            self._deallocate(block)
        return r

    # returns two hashes string or None
    def _collapse_branch_inner(self, block, pos, moddepth):
        if moddepth == 0:
            leafpos = from_bytes(block[pos + 8:pos + 10])
            if leafpos == 0xFFFF:
                r = self._collapse_branch(self._deref(block[pos:pos + 8]))
            else:
                r = self._collapse_leaf(self._deref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), block)
            if r != None:
                block[pos:pos + 10] = bytes(10)
            return r
        t0 = get_type(block, pos)
        t1 = get_type(block, pos + 32)
        if t0 == TERMINAL and t1 == TERMINAL:
            r = block[pos:pos + 64]
            block[pos:pos + 64] = bytes(64)
            return r
        if t0 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos + 32:pos + 64] = bytes(32)
            return r
        if t1 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 64, moddepth - 1)
            if r != None:
                block[pos:pos + 32] = bytes(32)
            return r
        return None

    def _catch_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        node = Node(leaf, rpos)
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, node.get_pos(1))
            if r != None:
                leaf[rpos + 66:rpos + 68] = bytes(2)
                leaf[rpos:rpos + 64] = r
            return
        if t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, node.get_pos(0))
            if r != None:
                node.set_pos(0, -1)
                node.set_hash(0, r[:32])
                node.set_hash(1, r[32:])
            return

    # returns two hashes string or None
    def _collapse_leaf(self, leaf, pos, branch):
        assert pos >= 0
        r = self._collapse_leaf_inner(leaf, pos)
        if r != None:
            inputs = leaf.get_inputs()
            if inputs == 1:
                if branch[:8] == self._addrof(leaf):
                    branch[:8] = bytes(8)
                self._deallocate(leaf)
                return r
            leaf.set_inputs(inputs - 1)
        return r

    # returns two hashes string or None
    def _collapse_leaf_inner(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        node = Node(leaf, rpos)
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        r = None
        if t0 == TERMINAL and t1 == TERMINAL:
            r = node.get_hash(0) + node.get_hash(1)
        elif t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, node.get_pos(1))
        elif t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, node.get_pos(0))
        if r is not None:
            # this leaf node is being collapsed, deallocate it
            next_entry = leaf.get_next_ptr()
            node.make_unused(next_entry)
            leaf.set_next_ptr(pos)
        return r

    # Convenience function
    def is_included(self, tocheck):
        return self.is_included_already_hashed(sha256(tocheck).digest())

    # returns (boolean, proof string)
    def is_included_already_hashed(self, tocheck):
        return self._is_included(set_terminal(tocheck))

    # returns (boolean, proof string)
    def _is_included(self, tocheck):
        buf = []
        self.get_root()
        t = get_type(self.root, 0)
        if t == EMPTY:
            return False, bytes([EMPTY])
        if t == TERMINAL:
            return tocheck == self.root, self.root
        assert t == MIDDLE
        r = self._is_included_branch(tocheck, self.rootblock, 8, 0, len(self.subblock_lengths) - 1, buf)
        return r, b''.join([bytes(x) for x in buf])

    # returns boolean, appends to buf
    def _is_included_branch(self, tocheck, block, pos, depth, moddepth, buf):
        if moddepth == 0:
            if block[pos + 8:pos + 10] == bytes([0xFF, 0xFF]):
                return self._is_included_branch(tocheck, self._deref(block[pos:pos + 8]), 8, depth, len(self.subblock_lengths) - 1, buf)
            else:
                return self._is_included_leaf(tocheck, self._deref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), depth, buf)
        buf.append(bytes([MIDDLE]))
        if block[pos:pos + 32] == tocheck or block[pos + 32:pos + 64] == tocheck:
            _finish_proof(block[pos:pos + 64], depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_branch(tocheck, block, pos + 64, depth + 1, moddepth - 1, buf)
            buf.append(_quick_summary(block[pos + 32:pos + 64]))
            return r
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(block[pos:pos + 32]))
            return self._is_included_branch(tocheck, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, buf)

    # returns boolean, appends to buf
    def _is_included_leaf(self, tocheck, block, pos, depth, buf):
        assert pos >= 0
        pos = 4 + pos * 68
        node = Node(block, pos)
        buf.append(bytes([MIDDLE]))
        if node.get_hash(0) == tocheck or node.get_hash(1) == tocheck:
            _finish_proof(node.get_hash(0) + node.get_hash(1), depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(node.get_hash(0) + node.get_hash(1), depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_leaf(tocheck, block, node.get_pos(0), depth + 1, buf)
            buf.append(_quick_summary(node.get_hash(1)))
            return r
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(node.get_hash(0) + node.get_hash(1), depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(node.get_hash(0)))
            return self._is_included_leaf(tocheck, block, node.get_pos(1), depth + 1, buf)

def _finish_proof(val, depth, buf):
    v0 = val[:32]
    v1 = val[32:]
    if get_type(v0, 0) == TERMINAL and get_type(v1, 0) == TERMINAL:
        b0 = get_bit(v0, depth)
        b1 = get_bit(v1, depth)
        if b0 == b1:
            if b0 == 0:
                buf.append(bytes([MIDDLE]))
                _finish_proof(val, depth + 1, buf)
                buf.append(bytes([EMPTY]))
            else:
                buf.append(bytes([EMPTY]))
                buf.append(bytes([MIDDLE]))
                _finish_proof(val, depth + 1, buf)
            return
    buf.append(_quick_summary(v0))
    buf.append(_quick_summary(v1))

def _quick_summary(val):
    t = get_type(val, 0)
    if t == EMPTY:
        return bytes([EMPTY])
    if t == TERMINAL:
        return val
    assert t == MIDDLE
    return set_invalid(val)
