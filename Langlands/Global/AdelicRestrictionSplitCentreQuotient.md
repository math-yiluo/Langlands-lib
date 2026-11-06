# Measures and Weil compatibility on the restriction split-centre quotient

Author: Worker 112.

Getz--Hahn (2.20), p. 68, define `A_G` through the greatest `ℚ`-split torus of
the restriction of scalars of the centre, and display (2.21), p. 69, forms
`[G] = A_G G(F) \ G(A_F)`. Display (2.22), p. 69, compares `[G]` with the
norm-one quotient `G(F) \ G(A_F)^1`. Source:
`getz-hahn-2024-automorphic-representations`.

The published module `AdelicRestrictionSplitCentre` defines this quotient for
supplied data, as `RestrictionSplitCentre.Quotient F G S j`, but gives it no
measure. The published `PositiveRealTorus` modules construct a quotient
measure, full subgroup Haar and Weil compatibility on a different quotient,
`PositiveRationalQuotient F G T i`. That quotient uses the positive image of
an `F`-split central torus `i : T.toGrp ⟶ G` of `G` itself. This module
carries those results over to `Quotient F G S j` whenever the two positive
images agree.

## Data and the comparison hypothesis

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` maps it into the published
  Weil restriction.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`.

Write `H = AdelicGroupPoints F G`. Below, `Γ = rationalSubgroup F G S j` is
the join of the restriction image `subgroup F G S j` with the principal
points, and `Γ' = positiveRationalSubgroup F G T i` is the join of
`imageSubgroup F T G i` with the same principal points.

Most results take the hypothesis
`h : subgroup F G S j = imageSubgroup F T G i`. This is exactly the
conclusion of the published proposition
`RestrictionSplitCentre.ComparisonStatement` for split components `j` and
`i`. This module does not prove that proposition. Results that need the
positive-torus measures also take the hypotheses of the published API:
- `hi`: `characterRestrict i` is injective;
- `characterRestrict i` has finite-index range;
- `hc : IsCentral i`;
- `hT : IsSplitTorus T.toGrp`.

## Generic transport along equal subgroups

These lemmas live in namespace `LeftCosetSpace` and hold for an arbitrary
group `H` and subgroups `Γ = Δ`. Each proof substitutes the equality, so both
comparison maps become the identity.
- `isMulRightInvariant_map_subgroupCongr`: if a measure on `Γ` is right
  invariant, so is its pushforward along `MulEquiv.subgroupCongr h`.
- `isHaarMeasure_map_subgroupCongr`: the same for Haar measures.
- `isCompatible_congrSubgroup`: suppose
  `IsCompatible Γ μH μΓ ν`, the measure `μΓ` pushes forward to `μΔ` under
  `MulEquiv.subgroupCongr h`, and `ν` pushes forward to `ν'` under the
  published `congrSubgroupHomeomorph h`. Then `IsCompatible Δ μH μΔ ν'`.
  The compatibility structure has no Borel-space parameter on the quotient,
  so no quotient Borel instance is assumed.

## Quotient measure, defined without the comparison hypothesis

- `normOneToQuotient F G S j` sends the class of a norm-one point `n` in
  `NormOneRationalQuotient F G` to the class of `n` in `Quotient F G S j`.
  It is well defined because principal norm-one points lie in `Γ`
  (`normOneToQuotient_mk`). `measurable_normOneToQuotient` proves it
  measurable.
- `quotientHaarMeasure F G S j` is the pushforward of the published
  `normOneRationalQuotientHaarMeasure F G` along this map. The definition
  uses no torus `T` and no comparison hypothesis.

## Identification with the positive-torus quotient

Assume `h`.
- `rationalSubgroup_eq` proves `Γ = Γ'`. The two joins have equal first
  arguments and the same second argument.
- `quotientHomeomorph F G h` is the published
  `congrSubgroupHomeomorph`, from `PositiveRationalQuotient F G T i` to
  `Quotient F G S j`. It sends `[x]` to `[x]` (`quotientHomeomorph_mk`)
  and commutes with right translation (`quotientHomeomorph_rightTranslate`).
- `quotientMeasurableEquiv F G h` is the same map as an equivalence of the
  inherited quotient sigma algebras. `quotientMeasurableEquiv_mk` and
  `quotientMeasurableEquiv_normOneToPositiveQuotient` give its values on
  classes.
- `measurePreserving_quotientMeasurableEquiv` proves that it carries
  `positiveRationalQuotientHaarMeasure F G T i` exactly to
  `quotientHaarMeasure F G S j`. `map_quotientHomeomorph` states this as an
  equality of pushforward measures. The proof composes the two pushforwards
  from the norm-one quotient.

## Topology: closedness, Hausdorffness, Borel structure, (2.22)

Assume `h`, `hi`, finite index, `hc` and `hT`.
- `isClosed_rationalSubgroup` proves that `Γ` is closed in `H`. The proof
  obtains finite splitting coordinates from `hT`, rewrites with
  `rationalSubgroup_eq`, and applies the published
  `isClosed_positiveRationalSubgroup`.
- `quotient_t2Space` proves that `Quotient F G S j` is Hausdorff.
- `quotient_borelSpace` proves that its inherited quotient sigma algebra is
  the Borel sigma algebra. It applies the published
  `LeftCosetSpace.quotient_borelSpace`.
- Fix finite splitting coordinates `e : T.toGrp ≅ splitTorus (Spec F) I`.
  `normOneQuotientHomeomorph F G hi h I e hc` is a homeomorphism from
  `NormOneRationalQuotient F G` to `Quotient F G S j`: the published
  `positiveQuotientHomeomorph` followed by `quotientHomeomorph`.
  `coe_normOneQuotientHomeomorph` proves that its underlying function is
  `normOneToQuotient F G S j`, independent of `I` and `e`. This is the
  shape of Getz--Hahn (2.22) for the supplied data, conditional on `h`.

## Subgroup Haar and orbital averages

Assume `h`, `hi`, finite index, `hc` and `hT`.
- `subgroupHaarMeasure F G hi h hc hT` is a measure on `Γ`. It is the
  published intrinsic full subgroup Haar
  `intrinsicPositiveRationalSubgroupHaarMeasure F G T i hi hc hT` on `Γ'`,
  pushed forward along `MulEquiv.subgroupCongr`, the identity on ambient
  points. That measure is normalized positive Haar times counting on
  principal norm-one points, transported by multiplication.
  `subgroupHaarMeasure_isMulRightInvariant` and
  `subgroupHaarMeasure_isHaarMeasure` follow from the generic lemmas. This
  normalization is derived internally from the published one; it is not
  claimed to be the measure normalization chosen in Getz--Hahn.
- `rationalQuotientAverage F G hi h hc hT f` is the published
  `quotientAverage` for `Γ` and this measure. By
  `rationalQuotientAverage_mk`, it sends `[g]` to
  `∫ k : Γ, f (k.val * g)`. The integral is Lean's total Bochner integral,
  so no convergence is asserted for arbitrary `f`.
- `rationalQuotientAverage_quotientHomeomorph` proves that this average at
  the class of `x` equals the published
  `intrinsicPositiveRationalQuotientAverage` at the class of `x`, for every
  `f`. The proof is change of variables along a measurable embedding.

## Weil compatibility

This section also assumes that Haar measure on `normOneSubgroup F G` is right
invariant, as the published positive-torus Weil theorem does.
- `quotientHaarMeasure_isCompatible` proves
  `IsCompatible Γ haar (subgroupHaarMeasure F G hi h hc hT)
  (quotientHaarMeasure F G S j)`. It applies `isCompatible_congrSubgroup` to
  the published `intrinsicPositiveRationalQuotientHaarMeasure_isCompatible`.
  So the quotient measure is nonzero and regular, every right translation
  preserves it, and the Weil formula holds for continuous compactly supported
  complex functions, together with integrability.
- `integrable_rationalQuotientAverage` and
  `integral_rationalQuotientAverage` state the last two fields separately:
  for continuous compactly supported `f`, the average is integrable, and
  `∫ q, A(f)(q) = ∫ g, f g ∂haar`.

## Independence of the split component of G

Let `T'`, `i'` be a second torus map, with injective finite-index character
restriction, and let `h'` be the corresponding comparison hypothesis.
`subgroupHaarMeasure_eq_of_splitComponents` proves that, for split components
`hs : IsSplitComponent i` and `hs' : IsSplitComponent i'`, the two
transported subgroup measures on `Γ` are equal. The proof uses the published
`measurePreserving_splitComponentSubgroupEquiv_intrinsic`. The quotient
measure does not depend on `T` or `i` at all.

## Use of the comparison statement

- `subgroup_eq_of_comparison`: given `hcomp : ComparisonStatement`,
  `hj : IsSplitComponent j` and `hs : IsSplitComponent i`, it derives `h`.
- `quotientHaarMeasure_isCompatible_of_comparison`: under the same
  hypotheses and `hi`, finite index and norm-one right invariance, it gives
  the Weil compatibility above.

`ComparisonStatement` appears only as a hypothesis.

## Provenance and scope

The quotient and the comparison (2.22) follow Getz--Hahn (2.20)--(2.22).
Every construction and proof here is internal. It combines published Library
objects using identity-on-representatives comparisons and Mathlib
change-of-variables results. No external theorem is asserted.

These remain separate obligations:
- the existence of split components `j` and `i`;
- the comparison statement itself;
- the remaining Getz--Hahn hypotheses (connected reductive `G`; the greatest
  `ℚ`-split torus in `Res_{F/ℚ} Z_G`);
- norm-one right invariance (unimodularity);
- finite volume and reduction theory.
