# Supercuspidal supports of subquotients of `ρ₀ × τ`

This internal helper module is the fourth of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`. Its main
result is `isSupercuspidalSupport_cons`. Let `A₀` be a supercuspidal
representative of a cuspidal datum `ρ₀`, and let `τ` have the supercuspidal
support `s`. Then every irreducible actual subquotient of `A₀ × τ` has the
supercuspidal support `ρ₀ ::ₘ s`. All declarations live in the namespace
`Langlands.Classification.SegmentHeadSupport`.

## Exact functors and products

- `PreservesShortExact.isSubquotient_map`: a functor that preserves short
  exact sequences (`SegmentHeadSupportGeneric`) sends actual subquotients to
  actual subquotients. Write the subquotient as an injection followed by a
  surjection (`SmoothRep.isSubquotient_iff_exists`). Apply
  `PreservesShortExact.map_injective` and `map_surjective` of
  `SegmentHeadSupportLeftExact`.
- `normalizedProductInductionFunctor_rankCast_obj`: product induction on a
  rank-cast block shape is the rank cast of product induction on the original
  shape. `binaryNormalizedProductFunctor_obj_eq` writes the binary product of
  positive ranks as product induction on `BlockShape.binary`. Both are copies
  of generic equations from the Library module `SegmentProductSplit`. That
  module is not imported, so that the import closure stays free of its other
  imports, such as `Classification.LanglandsData`.

## Rank casts and rank zero

- `rankCast_symm_obj`, `isSubquotient_rankCast_iff`, `isIrreducible_rankCast`
  and `isSupercuspidalSupport_rankCast_iff` move subquotients, irreducibility
  and supercuspidal supports across a rank cast `generalLinearRankCast`. Each
  is proved by `subst` on the rank equation.
- `finrank_eq_one_of_isIrreducible`: an irreducible smooth representation of
  `GL_0(F)` is one-dimensional. The group is trivial, so subrepresentations
  are exactly subspaces. A simple lattice of subspaces means dimension one
  (`isSimpleModule_iff_finrank_eq_one`).
- `nonempty_equiv_rankCast_product_right`: for a one-dimensional `Z` of rank
  zero, the rank-cast product `A × Z` is equivalent to the rank cast of `A`.
  It is the mirror image of `nonempty_equiv_rankCast_product_left` of
  `SegmentHeadSupportLeibniz`, using the published right unit law
  `T.binaryProductRightUnitEquiv`.

## Supports

The published `T.IsSupercuspidalSupport σ s` (Zelevinsky 1980, §1.10) says
that some ordering `ρ_1, …, ρ_k` of the multiset `s` has `σ` as an irreducible
actual subquotient of `T.cuspidalProductInduced`, the normalized product of
chosen supercuspidal representatives.

- `isSupercuspidalSupport_singleton`: an irreducible actual subquotient of the
  universe lift of a representative `A₀` of `ρ₀` has the support `{ρ₀}`. The
  one-factor product `T.cuspidalProductInduced` is equivalent to the lift of
  `A₀` by the published `T.singleBlockNormalizedProductEquiv`.
- `isSupercuspidalSupport_cons`. Let `τ` be an irreducible subquotient of
  `ρ_1 × ⋯ × ρ_k` with representatives `A_i`.
  - If `k = 0`, then `τ` has rank zero, so it is one-dimensional, and
    `A₀ × τ` is equivalent to the rank cast of the lift of `A₀`
    (`nonempty_equiv_rankCast_product_right`). The singleton lemma gives the
    support `{ρ₀} = ρ₀ ::ₘ 0`.
  - If `k ≥ 1`, then `A₀ × τ` is an actual subquotient of
    `A₀ × (A_1 × ⋯ × A_k)`, because `X ↦ A₀ × X` is exact
    (`preservesShortExact_binaryNormalized_sectR`). The published
    `T.headTailProductInductionIso` identifies the latter with the full product
    `A₀ × A_1 × ⋯ × A_k`, through the two shape equations above. This product is
    `T.cuspidalProductInduced` for the family `Fin.cons ρ₀ ρ`, whose multiset is
    `ρ₀ ::ₘ s`.

## Provenance and inputs

All statements are internal lemmas. They use only the published definitions
of supercuspidal support (Zelevinsky 1980, §1.10, registered source
`zelevinsky-1980-induced-ii`), of normalized product induction and of rank
casts, and the exactness proved in `SegmentHeadSupportLeftExact`.

Direct imports:

- `Langlands.Representation.Classification.SegmentHeadSupportLeibniz`.
- `Langlands.Representation.Classification.SupercuspidalSupport`, for
  `IsSupercuspidalSupport`, `cuspidalShape` and `cuspidalProductInduced`.
- `Langlands.Representation.Parabolic.HeadTailProductInduction`, for
  `headTailProductInductionIso` and the head/tail shape API.
- `Langlands.Representation.Induction.SingleBlock`, for
  `singleBlockNormalizedProductEquiv`.
- Mathlib's `RingTheory.SimpleModule.Rank`.

The complete closure audit is in
`SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
