# Continuous parabolic-vanishing functions in the almost-everywhere cuspidal `L²` subspace of the restriction split-centre quotient

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`L²_cusp([G])` in (6.20)--(6.21), printed p. 168 (PDF p. 182), by almost
everywhere vanishing of the integrals `∫_{[N]} φ(n g) dn` for every proper
parabolic. Definition 6.5.1 and (6.18), printed p. 167 (PDF p. 181), impose
the same vanishing at every `g` on automorphic forms.

On the restriction quotient `RestrictionSplitCentre.Quotient F G S j`, which
has the GH shape `A_G G(F) \ G(A_F)`, two constructions are available:

- `GroupSchemeRestrictionCuspidalL2` gives the `L²` classes of continuous
  square-integrable functions whose constant terms converge and vanish at
  every adelic point, and of continuous functions coming from the published
  `AdelicCuspidalForms`;
- `GroupSchemeRestrictionFullAEL2` gives the almost-everywhere condition
  `IsAEQuotientParabolicCuspidal` and, for the canonical measure, the closed
  subspace `quotientFullAEL2CuspidalSubmodule`.

This module shows that, for the mass-one measures
`properParabolicQuotientMeasure F G hPD hG` on the radical quotients, the
first construction lands in the second. It is the restriction-quotient
analogue of the published `GroupSchemeFullAEL2Continuous`.

## Data

As in `GroupSchemeRestrictionFullAEL2`: a number field `F : Type`, an affine
group scheme `G` locally of finite type, `hPD`, `hG`, and `S`, `j`. From the
section `Canonical` on: `T`, `i`, `h : subgroup F G S j = imageSubgroup F T G i`,
injectivity and finite index for `characterRestrict i`, `hc : IsCentral i`,
`hT : IsSplitTorus T`, and `hInv'`, right invariance of the canonical
measure `quotientHaarMeasure F G S j`. The intertwining results also assume
that Haar measure on the norm-one subgroup is right invariant.

## Continuous functions (no torus data)

- `quotientParabolicPeriodIntegrand_eq_constantTermIntegrand`: for a
  continuous `f`, the integrand `[n] ↦ f([n g])` equals the published
  `constantTermIntegrand` of the pullback `quotientContinuousPullback F G S j f`
  at `g`. Both send the class of `n` to `f([n g])`.
- `hasConvergentQuotientParabolicPeriod_of_continuous`: the integral converges
  at every norm-one point, by the published
  `hasConvergentNormalizedParabolicConstantTerm`.
- `quotientParabolicPeriod_eq_constantTerm`: the integral equals the
  published `constantTerm` of the pullback for the mass-one measure.
- `isAEQuotientParabolicCuspidal_of_continuous`: if `f` lies in
  `quotientParabolicCuspidalSubrepresentation` for the mass-one measures, then
  `f` satisfies `IsAEQuotientParabolicCuspidal`. Convergence and vanishing hold
  at every norm-one point, so in particular almost everywhere.

## Canonical measure

- `isAEQuotientParabolicCuspidal_congr`: for strongly measurable functions
  that agree almost everywhere for `quotientHaarMeasure F G S j`, the
  condition holds for one exactly when it holds for the other. The proof
  composes with the published identification `quotientMeasurableEquiv F G h`,
  which preserves measure, and applies the published
  `mem_aeParabolicCuspidalFunctionSubmodule_congr` on the positive-torus
  quotient.
- `quotientParabolicCuspidalL2ToLp_mem_fullAE`: the `L²` class of every
  element of `QuotientParabolicCuspidalL2Functions` (mass-one measures,
  canonical measure) lies in `quotientFullAEL2CuspidalSubmodule`. The class
  agrees almost everywhere with the continuous function, which is strongly
  measurable because the quotient is Borel (`quotient_borelSpace`).
- `quotientCuspidalFormL2Image_le_fullAE`: every element of
  `quotientCuspidalFormL2Image` for the canonical measure lies in
  `quotientFullAEL2CuspidalSubmodule`. Such a class is also the class of a
  continuous parabolic-vanishing function, through
  `quotientCuspidalFormL2ToContinuousParabolic`.
- `quotientParabolicCuspidalL2ToFullAE` is the codomain restriction of
  `quotientParabolicCuspidalL2ToLp` to the subspace, as an intertwining map
  into `quotientFullAEL2CuspidalRightAction`.
  `quotientFullAEL2CuspidalToLp_comp_quotientParabolicCuspidalL2ToFullAE`
  records that composing with the inclusion gives back the original map.
- `quotientParabolicCuspidalL2ToFullAE_injective`: the map is injective,
  because the canonical measure is positive on nonempty open sets
  (`quotientHaarMeasure_isOpenPosMeasure`).
- `quotientContinuousParabolicCuspidalL2Image_le_fullAE`: the algebraic image
  `quotientContinuousParabolicCuspidalL2Image` is contained in
  `quotientFullAEL2CuspidalSubrepresentation`.

## Split components

`splitComponentParabolicCuspidalL2Image_le_fullAE`: for split components `j`
and `i`, the image `splitComponentParabolicCuspidalL2Image` for the mass-one
measures is contained in `splitComponentFullAEL2CuspidalSubrepresentation`.
The published comparison supplies `h`.

## What is not claimed

- Only containment is proved. Nothing here shows that the continuous images
  are dense in, or equal to, the almost-everywhere cuspidal subspace.
- The containment uses the mass-one measures on the radical quotients. For
  other measure families the continuous construction has its own vanishing
  condition, which this module does not compare.
- `AdelicCuspidalForms` is the published finite-smooth form space; it is not
  identified here with the GH space of cusp forms.

## Provenance

This is an internal construction. Every statement either unfolds the
published definitions or transports a published result along the published
identification of the restriction quotient with the positive-torus quotient.
No external theorem is asserted.
