# Combinatorics of the inner blocks of a geometric piece

This module is internal to the proof of the left cuspidal derivative lemma. It records
combinatorial facts about the pieces of the geometric lemma (Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I*, §2.12 and §5) for two block shapes
`B` and `C` of `GL_n`, a minimal representative `w` (`IsMinimalRepresentative B C w`) and
intersection refinements `S` of `B` and `R` of `C` with
`sourceLevi F B C w = refinedLevi F B S` and `ConjugatesLevi (B.flatten S) (C.flatten R) w`.
Nothing here depends on the shapes having two blocks except where this is stated as a
hypothesis.

## Coordinates

* `index_val_of_val_eq_zero`: in a block numbered zero, the coordinate `B.index i b` is `b`.
* `flattenBlockEquiv_val_eq_zero`: the first inner block of the first block is the flattened
  block numbered zero.
* `blockIndex_eq_fst_flatten`: the block of a coordinate is the outer block of its flattened
  block.

## The source inner block

`sourceBlock hw q` is the inner block of `S` that the block bijection `blockEquiv hw` of the
flattened conjugation sends to the inner block `q` of `R`; it is defined by transporting `q`
through `C.flattenBlockEquiv R`, `(blockEquiv hw).symm` and `(B.flattenBlockEquiv S).symm`.

* `flattenBlockEquiv_sourceBlock`: the defining identity.
* `blockIndex_flatten_symm_apply`: `w⁻¹` sends a coordinate of the flattened target block `k'`
  into the flattened source block `(blockEquiv hw).symm k'`.
* `blockIndex_apply_sourceBlock`: `w` sends every coordinate of `sourceBlock hw q` into the
  block `q.1` of `C`.
* `size_sourceBlock`: `sourceBlock hw q` and `q` have the same size.

## Order statements

The proofs use the Library lemma `Geometric.refinement_lt_iff_of_sourceLevi`: inner blocks
of one block of `B` are ordered like the blocks of `C` into which `w` sends them.

* `val_eq_zero_of_blockIndex_eq`, `sourceBlock_snd_eq_zero`: an inner block of `S` sent into
  the first block of `C` is the first inner block of its block of `B` (otherwise an earlier
  inner block would be sent into an earlier block of `C`).
* `sourceIndex_strictMono`: inside one block of `C`, the flattened source blocks of the
  inner blocks strictly increase. This uses that `w⁻¹` is increasing on each block of `C`
  (the second clause of `IsMinimalRepresentative`) and that the blocks of a block shape are
  intervals in order (`blockIndex_monotone`).
* `sourceBlock_fst_strictMono`: in the first block of `C`, the source blocks of `B` strictly
  increase; equal outer blocks would force both inner indices to be zero.
* `length_le_of_sourceBlock`: hence the first block of `C` has at most `B.length` inner
  blocks.
* `sourceBlock_fst_val_of_length_two`: if `B` has two blocks and the first block of `C` has
  two inner blocks, the inner block number `l` comes from the block `l` of `B`.
* `refinement_length_le`: every block of `B` has at most `C.length` inner blocks, since its
  inner blocks go to strictly increasing blocks of `C`.

## The identity case

`eq_one_of_sourceBlock`: if `C` has two blocks, its first block consists of a single inner
block, and that inner block comes from the first block of `B`, then `w = 1`. Proof: the
source block is the flattened block number zero of `B.flatten S` and the target is the
flattened block number zero of `C.flatten R`; by `apply_index_eq` (applied to the flattened
minimal representative, `isMinimalRepresentative_flatten`) `w` fixes all coordinates below
`C.size j₀`. All remaining coordinates lie in the second block of `C`, on which `w⁻¹` is
increasing, and `w⁻¹` maps them to coordinates at least `C.size j₀`. Hence `w⁻¹` is strictly
increasing on `Fin n`, so it is the identity.
