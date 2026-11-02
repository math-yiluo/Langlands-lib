# Leibniz pieces of a derivative of `L × X` with supercuspidal `L`

This internal helper module is the third of six modules behind the proof of
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation`. Let `L` be
an irreducible supercuspidal representation of `GL_r(F)`, `r > 0`, and let `X`
be a smooth representation of `GL_b(F)`. The module shows that every
irreducible actual subquotient of the order-`d` derivative of `L × X` is an
actual subquotient of `L × X^(d)` or of `X^(d-r)`, each after the evident rank
cast. All declarations live in the namespace
`Langlands.Classification.SegmentHeadSupport`.

## Rank-zero helpers

- `subsingleton_of_isZero` and `isZero_of_subsingleton`: a smooth
  representation is a zero object of the smooth category exactly when its
  carrier is subsingleton.
- `subsingleton_rankCast`: rank casts `generalLinearRankCast` preserve
  subsingleton carriers.
- `subsingleton_rankCast_product`: a rank-cast binary normalized product with a
  subsingleton factor has a subsingleton carrier. This uses the published
  `T.isZero_binaryNormalizedProductFunctor_obj`.
- `nonempty_iso_unit`: a one-dimensional smooth representation of `GL_0(F)`
  is isomorphic to the published product unit `T.binaryProductUnit`. Both are
  one-dimensional, and `GL_0(F)` acts trivially on both
  (`representation_apply_of_rank_eq_zero`).
- `rankCastEquiv`: the rank cast of `B` is `B` composed with the
  entry-preserving reindex `finCongr`.
- `nonempty_equiv_rankCast_product_left`: for a one-dimensional `Z` of rank
  zero, the rank-cast product `Z × B` is equivalent to the rank cast of `B`.
  The proof composes `nonempty_iso_unit`, the published left unit law
  `T.binaryProductLeftUnitEquiv`, `liftEquiv` and `rankCastEquiv`.

These helpers follow the pattern of the generic rank-zero lemmas in the
Library module `TwoSupercuspidalBinaryProductBridge`. That module is not
imported, and none of these lemmas uses a two-supercuspidal result. Each is a
direct consequence of the published product and rank-cast definitions.

## The derivative pattern

`DerivativePattern T ψ A` is a local proposition for a smooth representation
`A` of `GL_a(F)`. It says that the derivatives of `A` of every order `i` with
`0 < i < a` have subsingleton carriers, and that the top derivative of `A` has
complex dimension one.

`derivativePattern_of_supercuspidal` proves this pattern for every irreducible
supercuspidal `A` of positive rank. It is the published
`Langlands.Classification.supercuspidalDerivatives` (Bernstein–Zelevinsky
1977, §4.4, the Gelfand–Kazhdan theorem), restated for rank `a = n + 1`.

## The Leibniz cases

`leibniz_cases` has the following hypotheses: `0 < r`, `d ≤ r + b`, `L` of
rank `r` with the derivative pattern, `X` of rank `b`, and an irreducible
`σ` that is an actual subquotient of the order-`d` derivative of `L × X`. It
concludes one of two cases.

1. `d ≤ b`, and `σ` is an actual subquotient of the rank cast of
   `L × X^(d)`.
2. `r ≤ d` and `d - r ≤ b`, and `σ` is an actual subquotient of the rank cast
   of `X^(d-r)`.

All products are over the factor universe `max uF uW`, as in the published
Leibniz filtration. The proof runs as follows.

- The published `generalLinearDerivativeLeibnizFiltration` (Bernstein–Zelevinsky
  1977, Corollary 4.14(c)) glues the derivative `(L × X)^(d)` from the pieces
  `L^(i) × X^(j)` with `i + j = d`, `i ≤ r` and `j ≤ b`
  (`leibnizSource`, `leibnizPiece`, `leibnizIndices`).
- The published `WeylBranchPieces.IsGluedFrom.exists_isSubquotient_piece`
  places the irreducible `σ` in one piece. The bridge
  `SmoothRep.isSubquotient_iff_representation` moves between actual smooth
  subquotients and representation-level subquotients.
- If `i = 0`, the piece is `L × X^(d)`. This is case 1.
- If `i = r`, then `L^(r)` is one-dimensional of rank zero, and
  `nonempty_equiv_rankCast_product_left` identifies the piece with the rank
  cast of `X^(d-r)`. This is case 2.
- If `0 < i < r`, then `L^(i)` is subsingleton, so the piece is subsingleton
  (`subsingleton_rankCast_product`). An irreducible representation is not
  subsingleton (`nontrivial_of_isIrreducible`), so this case cannot occur.

## Provenance and inputs

`leibniz_cases` is an internal consequence of Bernstein–Zelevinsky 1977,
Corollary 4.14(c) (the Leibniz filtration) and §4.4 (derivatives of
supercuspidal representations), both used through their published Lean
proofs. Registered source: `bernstein-zelevinsky-1977-induced-i`. No other
assertion from the literature is transcribed.

Direct imports:

- `Langlands.Representation.Classification.SegmentHeadSupportLeftExact`.
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`,
  for `generalLinearDerivativeLeibnizFiltration` and the indexing helpers of
  its statement module.
- `Langlands.Representation.Classification.SupercuspidalDerivativesProof`, for
  `supercuspidalDerivatives`.

The complete closure audit is in
`SegmentHeadDerivativeSupportTruncationProof.md`.

Author: Worker 890.
