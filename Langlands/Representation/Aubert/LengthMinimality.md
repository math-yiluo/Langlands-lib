# Inversion length and actual minimum block Weyl representatives

Author: Worker 194.

This internal finite-coordinate prerequisite connects inversion length on the
actual symmetric group to the Library's actual block Weyl minimum
representatives. It also applies this result to the previously constructed
two-sided support core. The rank is arbitrary, including zero. No
representation-theoretic or classification theorem is used.

`inversions w` is the finite set of pairs `(a,b)` with `a < b` and
`w b < w a`. `inversionLength w` is its cardinality. The term "length" in
these declarations means exactly this inversion count. This module does not
define a word metric or prove an equality with a separately defined Coxeter
word length.

`inversionLength_symm` is proved by the bijection
`(a,b) ↦ (w b,w a)` from inversions of `w` to inversions of `w.symm`.
For adjacent coordinates `a.val + 1 = b.val` with `w b < w a`,
`inversionLength_mul_swap_add_one` proves that right multiplication by
`Equiv.swap a b` reduces the count by exactly one. Its implementation
uses the pair map `(x,y) ↦ (swap a b x,swap a b y)`. Except for the two
ordered pairs of the adjacent coordinates, this swap preserves the order
of a pair. The new inversion set is consequently in bijection with the
old inversion set with `(a,b)` erased. The descent hypothesis treats the
exceptional pair, and self-inversion of the swap proves bijectivity.
The left-multiplication formula `inversionLength_swap_mul_add_one` follows
by applying the right-multiplication formula to the inverse permutation.

`swap_mem_blockWeyl` proves directly from the existing actual subgroup
definition that a swap of coordinates with the same block label preserves
that block shape. Suppose now that `w` has minimum inversion count on
`W_C w W_B`. A descent of `w` at an uncut source edge would allow right
multiplication by a swap in `W_B`, staying in the double coset and
strictly lowering inversion count. A descent of `w.symm` at an uncut
target edge would similarly allow left multiplication by a swap in `W_C`.
Both are impossible. The existing
`Geometric.isMinimalRepresentative_iff_descents` then yields
`IsMinimalRepresentative B C w`: `w` strictly increases inside each
source block, and its inverse strictly increases inside each target block.
This is `isMinimalRepresentative_of_minimum_inversionLength`.

`exists_minimum_inversionLength` uses the least natural number occurring
as an inversion count in the nonempty double coset. The preceding result
identifies such a minimum as an increasing-block representative.
The published `Geometric.weylDoubleCoset_injective` says that two such
representatives in the same double coset agree. Thus any increasing-block
representative is a minimum, giving
`isMinimalRepresentative_iff_minimum_inversionLength`.
If another element of the double coset had the same count, it too would
be a minimum and hence would be that same representative.
`inversionLength_lt_of_minimal_of_ne` therefore proves strict inequality
away from the representative.

The support application keeps every tail hypothesis explicit.
`singleton_drop_isMinimalRepresentative` assumes that every point of
`θ \ {w}` has inversion count at least that of `w` and that deleting `w`
changes `weylSupport B C θ`. The previously proved
`singleton_drop_forces_minimal` places the entire double coset in `θ`
and supplies minimum rank on it. The actual minimum-count theorem above
then gives the actual increasing-block conditions.

`singleton_drop_iff_minimal_of_length_tail` additionally assumes that
`w ∈ θ` and that every permutation of strictly larger inversion count
belongs to `θ`. Under these explicit conditions, the support changes if
and only if `w` is an increasing-block representative. For the reverse
direction, every other member of its double coset has strictly larger
count, so its entire double coset lies in `θ`; the singleton-change
criterion for the two-sided core applies. No ordering of equal-count
elements is required.

Finally, `adjacent_blockIndex_ne_iff_cut` uses the published actual
adjacent-swap criterion to detect whether an edge is a cut.
`isMinimalRepresentative_iff_cut_subsets` rewrites both block-order
conditions as the literal finite-set conditions
`permutationDescents w ⊆ B.cuts` and
`permutationDescents w.symm ⊆ C.cuts`.

The provenance is internal: the inversion bijections, swap inequalities
and uniqueness argument are proved directly using actual coordinate
permutations and the existing published minimum-representative and
block-cut APIs. The two-sided-core construction is imported from its
separate paired module, which records its corrected-source provenance.
This module constructs no open Bruhat support or length-compatible
ordering. It asserts no equality of actual Jacquet support images,
orbital-integral comparison, graded transition-map identity, exterior
sign, representation exactness or signed effectivity. In particular,
the length-tail assumptions in its support theorems remain obligations
for an actual chosen Bruhat filtration.
