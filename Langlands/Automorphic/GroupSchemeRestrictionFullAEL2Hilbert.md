# The Hilbert structure on the almost-everywhere cuspidal `L²` subspace of `[G]`

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`L²_cusp([G])` in (6.20)--(6.21), printed p. 168 (PDF p. 182), as the
`φ ∈ L²([G])` whose constant terms along every proper parabolic vanish almost
everywhere. Lemma 9.2.1, printed p. 242 (PDF p. 254), states that it is closed.
The published module `GroupSchemeRestrictionFullAEL2` implements this
subspace, `quotientFullAEL2CuspidalSubmodule`, on the restriction split-centre
quotient `RestrictionSplitCentre.Quotient F G S j`, which has the GH shape
`A_G G(F) \ G(A_F)`, and proves it closed and stable under right translation.

This module gives that subspace the Hilbert-space structure inherited from
`L²([G])`, its orthogonal projection, and the compatibility of the projection
with right translation and with the published positive-torus projection. It is
the restriction-quotient counterpart of the published positive-torus module
`GroupSchemeFullAEL2Hilbert`. Where `G` is connected reductive, it also removes
the separate hypothesis that Haar measure on the norm-one subgroup `G(A_F)^1`
is right invariant, using the published proof of that invariance.

## Data

- `F : Type` is a number field and `G` is a group scheme over `Spec F` whose
  underlying scheme is affine and locally of finite type.
- `hPD : ParabolicDynamicStatement` and `hG : IsConnectedReductive G` are the
  published hypotheses of `GroupSchemeRestrictionFullAEL2`.
- `S`, `j : S ⟶ AffineWeil.groupScheme ℚ F G`, `T`, `i : T ⟶ G` and
  `h : subgroup F G S j = imageSubgroup F T G i` are as there, with `hi`
  (injectivity of `characterRestrict i`), finite index of its range,
  `hc : IsCentral i` and `hT : IsSplitTorus T`.
- `μ` is the canonical measure `quotientHaarMeasure F G S j`, and `Sq` is
  `quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT` in `Lp ℂ 2 μ`.

## Norm-one right invariance from connected reductivity

- `normOneHaar_isMulRightInvariant_of_connectedReductive`: for connected
  reductive `G`, Haar measure on `AdelicGroupPoints.normOneSubgroup F G` is
  right invariant. This applies the published
  `AdelicGroupPoints.normOneHaarRightInvariant`, whose hypotheses (smoothness
  and connectedness of `G`) are fields of `IsConnectedReductive G`.
- `quotientHaarMeasure_rightInvariant_of_connectedReductive` and
  `quotientHaarMeasure_isOpenPosMeasure_of_connectedReductive`: under `h`,
  `hi`, finite index, `hc` and `hT`, the canonical measure `μ` is right
  invariant and positive on nonempty open sets. These are the published
  `quotientHaarMeasure_rightInvariant` and
  `quotientHaarMeasure_isOpenPosMeasure` with the norm-one hypothesis
  discharged as above.

## The cuspidal Hilbert space

These need no right-invariance hypothesis.

- `quotientFullAEL2CuspidalClosedSubmodule` packages `Sq` with its
  closedness, from the published `isClosed_quotientFullAEL2CuspidalSubmodule`
  and the invariance above.
- `QuotientFullAEL2CuspidalHilbertSpace` abbreviates `Sq`; its norm, topology
  and complex inner product are those of `Lp ℂ 2 μ`. The instance
  `quotientFullAEL2Cuspidal_completeSpace` states that it is complete, since
  it is closed in a complete space.
- `quotientFullAEL2CuspidalInclusionLI` is the inclusion of `Sq` into
  `Lp ℂ 2 μ` as a linear isometry.
- `quotientFullAEL2CuspidalOrthogonalProjection` is Mathlib's orthogonal
  projection of `Lp ℂ 2 μ` onto `Sq`, and
  `quotientFullAEL2CuspidalAmbientProjection` is the same projection with
  codomain `Lp ℂ 2 μ`. Its operator norm is at most one
  (`norm_quotientFullAEL2CuspidalOrthogonalProjection_le`), it fixes `Sq`
  (`quotientFullAEL2CuspidalOrthogonalProjection_inclusion`), its values lie
  in `Sq` (`quotientFullAEL2CuspidalAmbientProjection_mem`), and the vectors
  it fixes are exactly the published `quotientFullAEL2CuspidalLocus`
  (`quotientFullAEL2CuspidalAmbientProjection_eq_self_iff`).

## Right translation

This section assumes, as instance and hypothesis, right invariance of Haar
measure on `G(A_F)^1` and right invariance `hInv'` of `μ`, as the published
`quotientFullAEL2CuspidalRightAction` does. Write `ρ` for the published
`rationalQuotientL2RightAction` and `ρc` for its restriction to `Sq`.

- `quotientFullAEL2CuspidalRightTranslate a` is `ρc a` as a surjective
  linear isometry of `Sq`, with inverse `ρc a⁻¹`.
- `map_quotientFullAEL2CuspidalSubmodule_rightTranslate`: the published
  right-translation isometry of `Lp ℂ 2 μ` maps `Sq` onto `Sq`. Stability
  under `a` and under `a⁻¹` comes from the published
  `quotientFullAEL2CuspidalSubrepresentation`.
- `quotientFullAEL2CuspidalAmbientProjection_rightAction`: the ambient
  projection commutes with every `ρ a`, by Mathlib's
  `LinearIsometry.map_starProjection` and the previous item.
  `quotientFullAEL2CuspidalOrthogonalProjection_rightAction` is the same
  identity for the `Sq`-valued projection.
- `quotientFullAEL2CuspidalProjectionIntertwiner` is the projection as an
  intertwining map from `ρ` to `ρc`, and
  `quotientFullAEL2CuspidalProjectionIntertwiner_comp_inclusion` states that
  its composite with the published inclusion `quotientFullAEL2CuspidalToLp`
  is the identity.

No continuity of the action in the adelic variable is asserted.

## Comparison with the positive-torus projection

Here `T` is given with a split-torus isomorphism `e : T ≅ splitTorus I`, and
`hT` is the witness built from `I` and `e`.

- `map_fullAEL2CuspidalSubmodule_quotientL2Equiv`: the published isometry
  `quotientL2Equiv F G h` maps the published positive-torus subspace
  `fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` onto `Sq`. This follows
  from the published `mem_quotientFullAEL2CuspidalLocus_iff` and needs no
  right-invariance hypothesis.
- Assuming right invariance of Haar measure on `G(A_F)^1`, as the published
  positive projection does:
  `quotientFullAEL2CuspidalAmbientProjection_quotientL2Equiv` states that
  `quotientL2Equiv F G h` carries the published positive-torus projection
  `fullAEL2CuspidalAmbientProjection` to the ambient projection onto `Sq`, by
  Mathlib's `Submodule.starProjection_map_apply`.
  `quotientFullAEL2CuspidalOrthogonalProjection_quotientL2Equiv` is the same
  for the `Sq`-valued projections, through the published
  `fullAEL2CuspidalEquiv`.

## Split components

Assume `hj : IsSplitComponent j`, `hs : IsSplitComponent i`, `hi` and finite
index, but no right-invariance hypothesis. The published
`subgroup_eq_of_splitComponents` supplies `h`, and `hs` supplies `hc` and `hT`.

- `quotientHaarMeasure_rightInvariant_of_splitComponents_of_connectedReductive`
  and
  `quotientHaarMeasure_isOpenPosMeasure_of_splitComponents_of_connectedReductive`:
  `μ` is right invariant and positive on nonempty open sets.
- `splitComponentReductiveL2RightAction` is the published right regular
  representation on `Lp ℂ 2 μ` with that invariance.
- `isClosed_splitComponentFullAEL2CuspidalSubmodule_of_connectedReductive`:
  the published `splitComponentFullAEL2CuspidalSubmodule` is closed.
- `splitComponentFullAEL2CuspidalOrthogonalProjection` is the orthogonal
  projection onto it.
- `splitComponentReductiveFullAEL2CuspidalSubrepresentation` is the published
  cuspidal subrepresentation for this action, and
  `splitComponentFullAEL2CuspidalProjectionIntertwiner` is the orthogonal
  projection as an intertwining map onto it.

Only the split-component section and the measure theorems above discharge
the norm-one hypothesis. The right-translation and comparison sections keep it
as an explicit instance, so that they apply with any proof of it.

## Scope and what is not claimed

- `h`, injectivity and finite index of `characterRestrict i`, centrality and
  splitness of `i` (or the split-component hypotheses) remain hypotheses.
- Nothing here relates `Sq` to continuous or smooth cusp forms, asserts any
  density, or identifies the cuspidal subspace with a discrete spectrum or a
  trace-class operator (GH Theorem 9.1.2).

## Provenance

This is an internal construction. It applies the pinned Mathlib APIs for
closed submodules and orthogonal projections to the published subspace of
`GroupSchemeRestrictionFullAEL2`, and transports the published positive-torus
projection of `GroupSchemeFullAEL2Hilbert` along the published
`quotientL2Equiv`. No external theorem is asserted; GH (6.20)--(6.21) and
Lemma 9.2.1 are cited for the subspace and the closedness that the published
results supply.
