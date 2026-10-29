# The merged-slot Jacquet filtration from the geometric lemma

Author: Worker 890.

This module derives the statement
`Langlands.Classification.SegmentEdgeJacquetFiltration.{uF,uV,uW} F T`
(module `SegmentEdgeJacquetStatement`) from the normalized geometric lemma.
**It does not prove the geometric lemma**: the main results take
`GeometricLemmaTheorem` or `PadicGeometricLemmaTheorem` as an explicit
hypothesis. The other input, deletion of prescribed zero factors from a
filtration, is the published theorem
`ObjectRepFiltration.zeroFactorDeletionTheorem`. All declarations live in the
namespace `Langlands.Classification.SegmentEdge`. Provenance is internal: the
module assembles published constructions, following the mathematical derivation
recorded in the Markdown of `SegmentEdgeJacquetStatement` (Zelevinsky 1980,
1.2, 1.3 and 1.5(a); BZ77 2.12).

Notation: `B` is a block shape of rank `n`, `hk : k + 1 < B.length`,
`Γ = B.adjacentMerge k hk`, `S₀ = B.adjacentRefinement k hk` (a refinement of
`Γ`) and `e = B.adjacentBlockEquiv k hk`. The block sizes of `S₀ j` are by
definition the sizes of the corresponding blocks of `B`
(`BlockShape.adjacentBlock_size` is `rfl`), so the Levi of `S₀ j` is literally
`∀ t, GL(B.size (e ⟨j, t⟩))`.

## Main results

- `segmentEdgeJacquetFiltration_of_padicGeometricLemma`:
  `PadicGeometricLemmaTheorem.{uF, uW} → SegmentEdgeJacquetFiltration.{uF, uV, uW} F T`.
  It applies the previous theorem at rank `m * r`, which is positive because
  `k + 1 < m` and `0 < r`.
- `segmentEdgeJacquetFiltration_of_geometricLemma`: the same conclusion from
  `GeometricLemmaTheorem.{uF, uW} T Γ β` for every uniform shape
  `β = BlockShape.uniform m r hr` and every merge `Γ = β.adjacentMerge k hk`. It
  applies `edgeFiltration_of_geometricLemma` with `uniform_size_lt`.
- `edgeFiltration_of_geometricLemma`: for a general `B` satisfying
  `hsize : ∀ c c' d, c ≠ c' → B.size d < B.size c + B.size c'` and given
  `GeometricLemmaTheorem.{uF, uW} T Γ B`, the conclusion of
  `SegmentEdgeJacquetFiltration` holds for `B` in place of the uniform shape:
  for families `σ i` (universe `uV`) on the blocks of `B` and `Y j` (universe
  `uW`) on the blocks of `Γ` satisfying (H1) and (H2), the normalized `B`
  Jacquet module of `i_Γ(Y)` has an `ObjectRepFiltration` indexed by a bijection
  with `{v : MinimalConjugatingPermutations B B // IsMinimalRepresentative Γ B v}`,
  whose successive quotients are equivalent to `transport B B v (⊠ σ)`.

## Proof of `edgeFiltration_of_geometricLemma`

1. The geometric lemma gives refinements `S w` of `Γ` and `R w` of `B` with the
   intersection equalities, an enumeration `enum` of the minimal `(Γ, B)`
   representatives and a natural filtration of `jacquetInductionFunctor T Γ B`
   whose graded functors are isomorphic to the geometric pieces. Evaluating it
   at `ρ_Y = FiniteTensor.externalSmoothObject Y` (`objectFiltrationAt`) gives a
   filtration of the target Jacquet module. Its graded quotients are equivalent
   to the evaluated pieces (`Representation.equivOfIso`). Here
   `T.normalizedProductInductionFunctor Γ` is by definition the external tensor
   functor followed by `T.normalizedParabolicInductionFunctor Γ`.
2. Retained indices are those `i` with `ConjugatesLevi B B (enum i)`. For any
   other `i`, `exists_bad_block_of_not_conjugatesLevi` (module
   `SegmentEdgeCombinatorics`) gives a block `j` with `S j` proper and different
   from `S₀ j`; (H1) makes the factor Jacquet module of `Y j` along `S j` zero.
   Then `refinedJacquet_external_subsingleton` and `geometricPiece_subsingleton`
   make the piece zero.
3. `ObjectRepFiltration.zeroFactorDeletionTheorem` deletes the other indices.
   The retained indices are reindexed by `enum` and `retainedEquiv`.
4. For a retained index, `eq_adjacentRefinement_of_conjugatesLevi` gives
   `S (enum i) = S₀`, and `geometricPiece_equiv_of_conjugates` identifies the
   piece with `transport B B w (⊠ σ)`.

## The identification `geometricPiece_equiv_of_conjugates`

For `w` with `ConjugatesLevi B B w`, source refinement `S₀` and any target
refinement `R`, the piece
`(geometricPieceFunctor T Γ B w S₀ R hS hR).obj ρ_Y` is equivalent to
`transport B B w (⊠ σ)`, assuming (H2). The steps follow the definition of the
piece (inner Jacquet, relabel, transport, relabel, inner induction):

- `mergedJacquetEquiv`: the normalized refined Jacquet module of `⊠_j Y_j` along
  `S₀` is equivalent to `(⊠_i σ_i) ∘ refinedToLevi`. It composes
  `RefinedJacquetTensor.jacquetEquiv` (refined Jacquet of an external tensor
  product is the tensor product of the factor Jacquet modules), the external
  tensor product of the (H2) equivalences (`FiniteTensorFiltration.externalCongr`)
  and the inverse of `FiniteTensor.regroupEquiv` along `e`. The published
  `FiniteTensorFiltration.compCongr` pulls an equivalence back along a homomorphism.
- `refinedToLevi`: the homomorphism from `refinedLevi F Γ S₀` to `B.Levi F` given by
  the inverse of `refinedLeviEquiv` followed by the inverse of
  `FiniteTensor.regroupGroup` along `e`. `leviEmbedding_refinedToLevi` shows that
  it preserves the ambient matrix: `B.leviEmbedding (refinedToLevi x) =
  Γ.leviEmbedding x`. This follows from `leviEmbedding_regroup`, checked on matrix
  entries with `BlockShape.adjacent_index`.
- `subgroupEqualityCompEquiv` carries the equivalence across the equality
  relabeling `refinedLevi = sourceLevi`.
- `intersectionTransportEquivOf`: if `ψ : sourceLevi F B' C w →* D.Levi F`
  preserves ambient matrices and `ConjugatesLevi D C w`, then the intersection
  transport of a representation equivalent to `ρ ∘ ψ` is equivalent to
  `transport D C w ρ` restricted to the target intersection. This generalizes
  the published `intersectionTransportFullEquiv` (which is the case `D = B'`,
  `ψ` the inclusion). It is applied with `B' = Γ`, `C = D = B`.
- `sourceLevi_merge_eq_top`: the target intersection `sourceLevi F B Γ w⁻¹` is
  everything. This holds because `w⁻¹` conjugates the Levi of `B` into itself
  (`targetLevi_eq_top_of_conjugates`) and `leviSubgroup_le_merge`. So `R` is full.
  The published `subgroupEqualityEquiv` and `fullRefinedInductionEquiv` then
  identify the induced piece with `transport B B w (⊠ σ)`, which is smooth by
  `isSmooth_transport`.

## Vanishing lemmas

- `piTensorProduct_subsingleton`: an indexed tensor product with one zero factor
  is zero (each pure tensor has a zero coordinate,
  `MultilinearMap.map_coord_zero`).
- `refinedJacquet_external_subsingleton`: if the normalized Jacquet module of
  `Y j` along `S j` is zero for one `j`, then the normalized refined Jacquet
  module of `⊠ Y` along `S` is zero. This uses the linear equivalence
  `RefinedJacquetTensor.refinedCoinvariantsEquiv`.
- `geometricPiece_subsingleton`: a geometric piece vanishes when its inner
  refined Jacquet module does. Each later step preserves zero carriers
  (`subgroupEqualityFunctor_subsingleton`,
  `normalizedRefinedInductionFunctor_subsingleton`).

## Technical options

The module sets `backward.isDefEq.respectTransparency.types false`, as does the
published `AssociatedGeometricPiecesEquivalenceProof`. The theorems
`geometricPiece_equiv_of_conjugates` and `edgeFiltration_of_geometricLemma` use
`maxHeartbeats 1600000`.
