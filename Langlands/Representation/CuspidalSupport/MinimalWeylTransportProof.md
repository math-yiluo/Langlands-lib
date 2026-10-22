# Quasicuspidality of minimal whole-Levi Weyl transport

Authors: Worker 253, with Worker 76 (the quotient step
`isLeviQuasicuspidal_transport_of_refinement_images`, reused verbatim from
their shared draft for task b66849c9).

This proof targets the published `MinimalWeylTransportQuasicuspidalTheorem`
in `AssociatedGeometricPiecesStatement`. The final theorem
`minimalWeylTransportQuasicuspidal` quantifies the implicit prime `p` with
`Fact p.Prime`, an actual `PadicField F`, its topological data `T` and every
natural rank `n`, including zero. The field universe `uF` and the carrier
universe `uV` are independent. The closing `example` checks this unapplied
telescope. The underlying result `isLeviQuasicuspidal_transport` holds over
any field, for any complex representation of the source Levi. It uses only the
minimality and actual `ConjugatesLevi` hypotheses, with no smoothness,
irreducibility, admissibility, finite length or nonzero-input hypothesis.

## Block geometry of a conjugating permutation

Fix block shapes `B` and `C` of rank `n` and a permutation `w` with
`ConjugatesLevi B C w`.

1. `swap_mem_blockWeyl_iff`: a transposition `swap a b` preserves the blocks
   of `B` exactly when `a` and `b` lie in the same block.
2. The imported `conjugatesLevi_inv` from
   `MinimalConjugatingCosetsProof` (Worker 165) says that `w⁻¹` conjugates the
   Levi of `C` onto that of `B`.
3. `blockIndex_eq_iff_of_conjugatesLevi`: `w a` and `w b` lie in the same
   `C`-block if and only if `a` and `b` lie in the same `B`-block. Apply the
   published `conjugatesLevi_weyl_mem` (for `w`, or for `w⁻¹` via step 2) to
   a block-preserving transposition. Mathlib's `Equiv.swap_apply_apply`
   identifies the conjugated transposition with the transposition of the
   images, and step 1 converts in both directions.
4. The shared `blockMap B C w i` from `BlockMap` is the `C`-block containing the image of the first
   coordinate of the `B`-block `i`. By step 3, every coordinate of block `i`
   is sent into this block (`blockIndex_apply_eq_blockMap`). The map is
   injective by step 3 and surjective via `w⁻¹`, giving `blockEquiv`.
5. `innerMap hw i a` is the position of `w (B.index i a)` inside the target
   block `blockMap B C w i`. It is chosen through the published
   `exists_index_of_blockIndex_eq`. It is bijective because `w` and the block
   coordinate maps are injective and `w⁻¹` returns a target block into block
   `i`. Hence `size_blockMap`: corresponding blocks have equal sizes.
6. `apply_index_eq`: under `IsMinimalRepresentative B C w`, the first
   minimality clause (`w` is increasing on each `B`-block) and the published
   `index_strictMono` for the target block coordinates make `innerMap hw i`
   strictly monotone. A strictly
   monotone bijection between `Fin` types of equal size has the same range as
   `Fin.cast`. Mathlib's `StrictMono.range_inj_of_wellFoundedLT` then gives
   `innerMap hw i = Fin.cast (size_blockMap hw i)`, that is
   `w (B.index i a) = C.index (blockMap B C w i) (Fin.cast _ a)`.
7. `leviConjugation_symm_block_entry`: for `m` in the Levi of `C`, the `i`-th block
   of `(leviConjugation B C w hw).symm m` has entries
   `m (blockMap B C w i) (Fin.cast _ a) (Fin.cast _ b)`. This uses the
   published `leviConjugation_symm_embedding`, the permutation-matrix entry
   lemmas and step 6.

## Transport of proper refinements and radicals

`castShape h D` regards a block shape of rank `k` as one of an equal rank `l`,
with the same blocks. Membership of a matrix in its standard parabolic or
unipotent radical is unchanged when the entries are recast along `h`
(`mem_castShape_parabolic_iff`, `mem_castShape_unipotentSubgroup_iff`, by
`subst`).

For a refinement `R` of `C`, `pullbackRefinement hw R` refines block `i` of
`B` by `R (blockMap B C w i)`, recast along `size_blockMap`. Using step 7 and
reindexing the blocks along `blockEquiv`, an element `m` lies in the refined
parabolic (resp. refined unipotent radical) of `C` for `R` exactly when
`(leviConjugation B C w hw).symm m` lies in the one of `B` for the pullback
(`mem_refinedParabolic_pullback_iff`, `mem_refinedUnipotent_pullback_iff`).
Consequently:

- `refinedUnipotent_map_leviConjugation_symm`: the image of the refined
  radical of `C` for `R` under the inverse Levi conjugation equals the refined
  radical of `B` for the pullback.
- `refinedParabolic_pullback_ne_top`: if the refined parabolic of `C` for `R`
  is proper, so is that of `B` for the pullback. Otherwise every element of
  the `C`-Levi would lie in the refined parabolic for `R`.

## Quotient step and conclusion

`isLeviQuasicuspidal_transport_of_refinement_images` (Worker 76) takes the
transport premise of the two previous results. Let `R` be a proper refinement
of `C`. The published `Jacquet.coinvariantsMapEquiv` from `GroupTransport`
identifies the coinvariants of `transport B C w hw ρ` by the refined radical
of `R` with the coinvariants of `ρ` by the image of that radical under the
inverse Levi conjugation. By the radical identification this image is the
refined radical of the proper pullback refinement. Quasicuspidality of `ρ`
makes those coinvariants subsingleton, and the injective equivalence transfers
this. `isLeviQuasicuspidal_transport` supplies the pullback refinement, and
`minimalWeylTransportQuasicuspidal` applies it to the representation of a
smooth source representation and to the value of a minimal representative.

## Provenance

The statement Markdown cites BZ77 2.4 (quasicuspidality via vanishing Jacquet
modules) and the quasicuspidality assertion of 2.13(c), with the geometry of
2.11–2.12 (registered `bernstein-zelevinsky-1977-induced-i`, printed
pp. 446, 448–449). This proof implements item 4 of that Markdown's proof
outline in the Library's actual product coordinates. The block bijection, the
order-preserving inner map and the recast refinements are internal
formalization devices with no separate literature counterpart.
