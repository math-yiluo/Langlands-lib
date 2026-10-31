# Chamber coordinates of standard intersections

Author: Worker 828.

Module `Langlands.Representation.Geometric.IntersectionChamberCoordinates`.

Fix block shapes `B`, `C` of rank `n`, a permutation `w`, and a refinement
`S : BlockRefinement B` with `hS : sourceLevi R B C w = refinedLevi R B S`.
The geometric lemma supplies such an `S` for each minimal double-coset
representative. This module shows three things:

- `w` carries every flattened block of `S` into a single block of `C`.
- Inverse Weyl transport carries block scalars of `C` to flattened block
  scalars of `S`, reindexed by a "chamber index".
- For a minimal representative, the chamber index is monotone inside each
  block of `B`.

All declarations are in namespace `Langlands.Geometric`. They are internal
coordinates and helper lemmas, written for the proof of
`Langlands.GLInductionWeakJacquetBoundsStatement` (task
5c9a0e18-0039-4f00-81bc-e103757b5a3a) and for reuse by the coarse-character
reflection of geometric pieces.

## Declarations and proofs

- `blockScalar_entry D a x y`: the `(x, y)` entry of `D.blockScalar R a` is
  `a (blockIndex D x)` if `x = y`, and `0` otherwise. Proof: write `x` and `y`
  as block coordinates (`TotalConjugatingCount.index_surjective`) and use
  `blockScalar_apply_same` and `blockScalar_apply_ne`.
- `blockIndex_eq_of_sourceLevi_eq B C w S hS h`: let `x`, `y` lie in the same
  block of the flattened shape `B.flatten S`. Then `w x` and `w y` lie in the
  same block of `C`, provided `R` is a nontrivial commutative ring. Proof:
  `x` and `y` lie in one block `i` of `B`, at positions `a` and `b`, in the
  same inner block of `S i`. Suppose `w x` and `w y` lie in different blocks
  of `C`. Let `m ∈ B.Levi R` have the permutation matrix of `swap a b` in
  block `i` and `1` elsewhere. Then `m` lies in `refinedLevi R B S`, by the
  entry criterion `CuspidalSupport.levi_mem_iff` and `permutation_entry`,
  since `swap a b` preserves the inner blocks. By `hS`, `m` lies in
  `sourceLevi R B C w`. But `mem_sourceLevi_iff` forces the entry of `m` at
  `(a, b)` to vanish, because `w x` and `w y` lie in different blocks of `C`.
  That entry is `1`, a contradiction.
- `chamberIndex B C w S k`: the block of `C` containing the image under `w`
  of the first coordinate of flattened block `k`.
- `chamberIndex_blockIndex`: under `hS`, `chamberIndex (blockIndex
  (B.flatten S) x) = blockIndex C (w x)` for every coordinate `x`.
- `chamberIndex_flattenBlockEquiv`: the same, written for the inner block
  `i` of outer block `j` at any position `r`.
- `monotone_chamberIndex B C w S hS hw j`: assume `w` is strictly increasing on
  every block of `B`, which is the first condition of
  `IsMinimalRepresentative`. Then `i ↦ chamberIndex (B.flattenBlockEquiv S ⟨j, i⟩)`
  is monotone. Proof: compare the first coordinates of inner blocks
  `i ≤ i'`. The coordinates are ordered by `index_lt_index_of_block_lt`, `w`
  preserves that order on block `j`, and `blockIndex C` is monotone
  (`blockIndex_monotone`).
- `flattenedBlockScalar B S R`: the flattened block scalars
  `(B.flatten S).blockScalarLevi R`, followed by the published
  `flattenedLeviEquiv R B S` into the actual refined Levi. Its composite is
  the homomorphism used in the source premise of the target statement
  (`flattenedBlockScalar_apply`). `flattenedBlockScalar_commute` shows its
  values are central in the refined Levi. `continuous_flattenedBlockScalar`
  shows it is continuous for a topological ring `R`, from continuity of
  `flattenedLeviEquiv` and of `GeneralLinear.scalar`.
- `chamberRestriction B C w S R`: the homomorphism sending `a : Fin C.length → Rˣ`
  to `k ↦ a (chamberIndex B C w S k)`.
- `intersectionLeviConjugation_symm_blockScalar`: let `m ∈ sourceLevi R C B w⁻¹`
  have underlying element `C.blockScalarLevi R a`. Then the published inverse
  transport `(intersectionLeviConjugation R B C w).symm m` has underlying
  element `flattenedBlockScalar B S R (chamberRestriction B C w S R a)`.
  Proof: embed into `GL n` (`intersectionLeviConjugation_symm_embedding`,
  `flattenedLeviEquiv_embedding`). There the claim says that conjugating the
  diagonal matrix of `a ∘ blockIndex C` by the permutation matrix of `w` gives
  the diagonal matrix of `a ∘ blockIndex C ∘ w`. That follows from
  `permutation_conjugate_entry`, `blockScalar_entry` and
  `chamberIndex_blockIndex`.

## Provenance and scope

Provenance: internal. The definitions `chamberIndex`, `chamberRestriction`
and `flattenedBlockScalar` are bookkeeping coordinates introduced for this
formalization. No source defines them under these names. They encode the
chamber comparison in Waldspurger 2003, III.2.3 (registered
`waldspurger-2003-plancherel`, printed pp.266–267), with the inverse
representative of the geometric lemma's pieces (Bernstein–Zelevinsky 1977,
2.11–2.12, registered `bernstein-zelevinsky-1977-induced-i`). In the source,
the inverse Weyl element maps the ambient positive chamber into the
within-block chambers of the source. Here the inverse transport is the
published `intersectionLeviConjugation`. The scalars on the fine blocks of
`S` are constant, so no block-size factor appears. The module contains no
spectral or analytic statement.
