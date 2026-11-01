# Balanced-quotient induction adjunction for jointly continuous atlas actions

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

Let `K : Type u` be a complete normed ultrametric field, `G : Type z`
a topological group, and `H` an open subgroup. Source and target are the
full categories `PointContinuousNonemptyAtlasAction K H` and
`PointContinuousNonemptyAtlasAction K G`, with presentation universes
`{u, max z v, max z w}`. Their objects have nonempty original chart
spectra and jointly continuous original point actions; their arrows are
the full chosen equivariant bounded atlas arrows.

`pointContinuousSourceNormalizationIso` exposes the existing
`NonemptyAtlasAction.normalizationIso` after `toNonempty`, with its source
typed as `normalizedAction H X.obj` and its target as the original action.
Its inverse naturality is the existing full-arrow naturality after the
same forgetful functor. This adapter retains the exact constructed
bounded maps while making the category endpoints explicit.

`pointContinuousHomEquiv` constructs
`Hom(pointContinuousQuotientFunctor H hH X, Y) ≃
Hom(X, pointContinuousRestriction H Y)`.
The source on the right is the original supplied source. To obtain it,
the forward map first uses `quotientActionExtensionEquiv` to restrict
through the actual quotient unit from the normalized source, then
precomposes with the inverse of the bounded normalization isomorphism.
That inverse exists by the explicit nonempty-spectrum condition on every
original chart. The inverse correspondence composes the original supplied
arrow with the forward normalization and uses the actual bounded quotient
extension. Both directions are complete equivariant arrows.

The two inverse laws use the previously proved quotient restriction and
extension identities, associativity, and the normalization isomorphism's
inverse identities. The two application lemmas expose these exact
constructions. Joint continuity of the original point action supplies
the precise `ContinuousSMul H (LocalSpace H X.obj)` instance locally;
the output quotient action and its continuity were constructed in
`AtlasContinuousQuotient`.

`pointContinuousHomEquiv_naturality_left` uses full quotient source
naturality and inverse normalization naturality after forgetting only the
point-continuity condition. Target naturality uses full quotient target
naturality and associativity. Inverse source naturality follows by
injectivity of the constructed equivalence. These are equalities of
complete bounded atlas arrows, including chart indices and algebra maps.
No equality of algebra maps is inferred from equality on spectrum points.

`pointContinuousAdjunction` packages these naturalities with
`Adjunction.mkOfHomEquiv`, proving that actual balanced-quotient induction
is left adjoint to continuous subgroup restriction. The final theorem
identifies its Hom equivalence with `pointContinuousHomEquiv`.

The provenance is internal assembly of the constructed relative quotient
correspondence, the conditional bounded normalization isomorphism and
the continuous full-subcategory functors. No quotient geometry,
extension arrow, or adjunction is assumed as input. Arbitrary subgroup
index, overlapping charts and empty spaces with no charts are allowed.
Continuity into an analytic automorphism topology, refinement
localization, analytic sites and Harris tower specialization remain
separate obligations.
