# Block combinatorics of an adjacent merge

Author: Worker 890.

This module is internal block combinatorics. It is used by
`Langlands.Representation.Classification.SegmentEdgeJacquetReduction` to decide
which pieces of the geometric lemma survive for an induction from a merged
shape. It cites no literature. Everything is stated in the existing coordinates:
`blockIndex D a` is the block of the coordinate `a : Fin n` in the shape `D`,
`D.index i x` is coordinate `x` of block `i`, and for a block shape `B` with
`hk : k + 1 < B.length`,

- `Γ = B.adjacentMerge k hk` merges blocks `k` and `k + 1` of `B`;
- `B.adjacentRefinement k hk` is the refinement of `Γ` that splits the merged
  block back into blocks `k` and `k + 1` and leaves every other block whole;
- `B.adjacentBlockEquiv k hk` is the lexicographic bijection from pairs (block of
  `Γ`, inner block) to the blocks of `B`.

All declarations live in the namespace `Langlands.Classification.SegmentEdge`.

## Shapes

- `blockIndex_le_iff D a b`: `blockIndex D a ≤ blockIndex D b` exactly when
  `a ≤ b` or `a` and `b` lie in the same block.
- `eq_of_sameBlock`: two block shapes `D, D'` of the same rank `n` are equal if,
  for all coordinates `a, b`, `a` and `b` lie in the same block of `D` exactly
  when they lie in the same block of `D'`.

  Proof: the map sending a block `i` of `D` to the `D'`-block of its first
  coordinate is strictly increasing (by `blockIndex_le_iff`) and surjective, so
  the two shapes have the same length and the map is the identity
  (`StrictMono.eq_id`). Then the block sizes agree, since each size counts the
  coordinates of its block (`TotalConjugatingCount.card_blockIndex_fiber`), and
  `BlockShape.ext_of_size` concludes.

## The adjacent merge

- `blockIndex_merge_index`: coordinate `a` of block `j` of `Γ` lies in block
  `B.adjacentBlockEquiv k hk ⟨j, t⟩` of `B`, where `t` is the block of `a` in the
  adjacent refinement of block `j` (from `BlockShape.adjacent_index`).
- `sameBlock_merge_iff`: two coordinates of one block `j` of `Γ` lie in the same
  block of `B` exactly when they lie in the same block of the adjacent
  refinement of block `j`.
- `mergeBlock_eq_of_blockIndex_eq`: coordinates in the same block of `B` lie in
  the same block of `Γ`.
- `isMinimalRepresentative_of_merge`: if `w` is a minimal representative for
  `(Γ, B)` then it is a minimal representative for `(B, B)`. (Increasing on each
  block of `Γ` implies increasing on each block of `B`; the condition on `w⁻¹` is
  the same.)

## Source-Levi intersections

Let `D, C` be block shapes, `w` a permutation and `S` a refinement of `D` with
`hS : sourceLevi F D C w = refinedLevi F D S` (over any field `F`).

- `mulSingle_swap_entries_iff`: for any labels `lab i` of the coordinates of each
  block `i`, the Levi element equal to the transposition matrix of `a, b` in
  block `j` and to the identity elsewhere has zero entries between all pairs of
  coordinates with different labels exactly when `a` and `b` have the same
  label.
- `sameBlock_of_sourceLevi_eq`: for coordinates `a, b` of block `j` of `D`,
  `a` and `b` lie in the same block of `S j` exactly when `w` sends
  `D.index j a` and `D.index j b` into the same block of `C`. Proof: test the
  equality `hS` on the element of `mulSingle_swap_entries_iff`, using the
  entrywise descriptions `mem_sourceLevi_iff`, `mem_refinedLevi` and
  `levi_mem_iff`.

## Levi-conjugating permutations of the merged shape

Here `S` is a refinement of `Γ` with
`hS : sourceLevi F Γ B w = refinedLevi F Γ S`.

- `blockIndex_apply_eq_of_trivial_or_adjacent`: if every `S j` has at most one
  block or equals the adjacent refinement of block `j`, then `w` sends any two
  coordinates of one block of `B` into one block of `B`.
- `conjugatesLevi_of_trivial_or_adjacent`: assume moreover
  `hsize : ∀ c c' d, c ≠ c' → B.size d < B.size c + B.size c'` (no two blocks of
  `B` fit together into one block of `B`). Then `ConjugatesLevi B B w`. Proof:
  by the previous lemma `w` maps block `c` of `B` into a block `d c`. If
  `d c = d c'` with `c ≠ c'`, then `w` injects both blocks into block `d c`, so
  `B.size c + B.size c' ≤ B.size (d c)`, contradicting `hsize`. So `d` is
  injective and `TotalConjugatingCount.conjugatesLevi_iff` applies.
- `eq_adjacentRefinement_of_conjugatesLevi`: if `ConjugatesLevi B B w`, then
  `S = B.adjacentRefinement k hk`. Proof: `eq_of_sameBlock` on each block,
  combining `sameBlock_of_sourceLevi_eq`, `conjugatesLevi_iff` and
  `sameBlock_merge_iff`.
- `exists_bad_block_of_not_conjugatesLevi`: under `hsize`, if `w` does not
  conjugate the Levi of `B` onto itself, then some `S j` has at least two blocks
  and differs from the adjacent refinement of block `j` (the contrapositive of
  `conjugatesLevi_of_trivial_or_adjacent`).
- `retainedEquiv`: the equivalence between the minimal `(Γ, B)` representatives
  `w` with `ConjugatesLevi B B w` and the elements `v` of
  `MinimalConjugatingPermutations B B` with `IsMinimalRepresentative Γ B v`. Both
  directions keep the underlying permutation; the forward direction uses
  `isMinimalRepresentative_of_merge`.
- `uniform_size_lt`: the uniform shape `BlockShape.uniform m r hr` satisfies
  `hsize`, since every block has size `r` and `r < r + r` for `r > 0`.
