# Finite volume of the restriction split-centre quotient

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.ConnectedReductiveQuotientFiniteVolumeStatement`
is a Prop-valued target. It states that the adelic quotient
`[G] = A_G G(F) \ G(𝔸_F)` of Getz–Hahn (2.21) has finite volume when `G` is
connected reductive over a number field. Here `A_G` comes from a split component of the
Weil restriction. The module defines this proposition and proves two total-mass lemmas.
It also proves that the published norm-one finite-volume target implies the new one. It
does not prove finite volume.

## Data

- `F : Type` is a number field in universe zero, as in the published
  `AdelicRestrictionSplitCentre` module.
- `G` is a group scheme over `Spec F` with `IsAffine G.X.left` and
  `LocallyOfFiniteType G.X.hom`.
- `S` is a commutative group scheme over `ℚ`, and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` maps it into the published affine Weil
  restriction.

The carrier is the published `Quotient F G S j`: the left quotient of
`AdelicGroupPoints F G` by `rationalSubgroup F G S j`, the join of the restriction image
of the positive real points of `S` with the principal points. The measure is the
published `quotientHaarMeasure F G S j`. It is the pushforward of
`AdelicGroupPoints.normOneRationalQuotientHaarMeasure F G` along `normOneToQuotient`,
the map `[n] ↦ [n]` from `G(F) \ G(𝔸_F)¹` to `Quotient F G S j`. This is the map of
Getz–Hahn (2.22). The definition uses no torus of `G` and no comparison hypothesis.

## Results

- `quotientHaarMeasure_univ`: `quotientHaarMeasure F G S j univ` equals
  `normOneRationalQuotientHaarMeasure F G univ`. The preimage of `univ` under
  `normOneToQuotient` is `univ`. The lemma holds for every `j`, with no reductivity or
  splitness hypothesis.
- `quotientHaarMeasure_isFiniteMeasure_iff`: `quotientHaarMeasure F G S j` is a finite
  measure if and only if `normOneRationalQuotientHaarMeasure F G` is. Both sides say the
  total mass is finite, so the previous lemma gives the equivalence. It also holds for
  every `j`. It compares total masses only and does not identify the two measures.
- `ConnectedReductiveQuotientFiniteVolumeStatement` (the target): for every number
  field `F : Type`, every `G` as above with `IsConnectedReductive G`, every `S` and
  every `j` with `GroupScheme.IsSplitComponent j`, `quotientHaarMeasure F G S j` is a
  finite measure. `IsConnectedReductive` is the Library definition in
  `Langlands.GroupScheme.Reductive.Basic`. `IsSplitComponent` is the Library
  definition in `Langlands.GroupScheme.Rational.Characters`: a central split torus
  through which every factorization via a central split torus is an isomorphism.
- `connectedReductiveQuotientFiniteVolumeStatement_of_normOne`: the published target
  `AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement.{0}` implies the new
  target. The proof applies the published target to `G` and uses the equivalence above.
  The split-component hypothesis is not used. The universe is zero because the
  quotient's number field lives in `Type`.

## Why the hypotheses restrict to reductive groups and split components

By the equivalence above, finiteness of `quotientHaarMeasure F G S j` depends only on
`G`, not on `j`. The hypotheses restrict the target to a case where the source
justifies the published measure as its measure on its quotient `[G]`.

- Getz–Hahn, printed p.69, say that under Lemma 2.6.2 (`G` reductive) and over a
  number field, (2.22) is a homeomorphism. They conclude that "if G is reductive for
  many purposes one can work with either `A_G G(F) \ G(𝔸_F)` or `G(F) \ G(𝔸_F)¹`."
  So for reductive `G` over a number field, this homeomorphism justifies taking the
  pushforward along (2.22) as the measure on `[G]`. Getz–Hahn also state that the
  conclusions of Lemma 2.6.2 can fail for a general affine algebraic group (their
  Exercise 2.19 asks for an example). Reductivity is a sufficient hypothesis here, not a
  necessary one. This module asserts no comparison of the two quotients for arbitrary
  affine `G`.
- Take a split component `j`, and a split component `i : T.toGrp ⟶ G` whose
  `characterRestrict i` is injective with finite-index range. Then the published
  `quotientHaarMeasure_isCompatible_of_comparison` applies, with
  `ComparisonStatement` proved in the Library as `RestrictionSplitCentre.comparison`.
  It proves that `quotientHaarMeasure F G S j` is Weil compatible with full Haar
  measure on `AdelicGroupPoints F G` and the published subgroup Haar measure. That
  theorem takes right invariance of norm-one Haar as a hypothesis (an instance
  argument). For smooth connected `G`, hence for connected reductive `G`, this
  hypothesis is supplied by the published `AdelicGroupPoints.normOneHaarRightInvariant` in
  `Langlands.Global.AdelicNormOneHaarRightInvariantProof`. This module invokes neither
  the compatibility theorem nor that proof. The compatibility is the reason the target
  is stated for split components.

## Source

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §2.6. Display
(2.20), printed p.68, defines `A_G`. Display (2.21), printed p.69 (PDF p.86), defines
`[G]`. Display (2.22) and the paragraph after it, printed p.69, compare `[G]` with
`G(F) \ G(𝔸_F)¹` for reductive `G`. Theorem 2.6.3 (Borel, Conrad, Harder, Oesterlé),
printed p.69, says `G(F) \ G(𝔸_F)¹` has finite volume for smooth connected `G`.
Getz–Hahn state no separate finite-volume theorem for `[G]`. The target is that
theorem for reductive `G` transported along (2.22). This transport is derived here and
is the content of `connectedReductiveQuotientFiniteVolumeStatement_of_normOne`.
Exercise 2.19, printed p.75 (PDF p.92), is cited only for the possible failure of
Lemma 2.6.2 for general affine groups. The October 2026 author errata have no
Chapter 2 entry.

Source records: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, §2.6, (2.20)–(2.22)
and Theorem 2.6.3, printed pp.68–69 (PDF pp.85–86); `getz-hahn-2024-errata-2026-10`,
SHA-256 `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

## Scope

This module proves no finite volume, compactness criterion, Siegel-set covering or
reduction theory. It does not prove that split components exist, and it does not
itself prove or use right invariance of norm-one Haar. It does not compare `quotientHaarMeasure` with any other
normalization of the measure on `[G]`.
