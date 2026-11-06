# The almost-everywhere cuspidal `L²` subspace of the restriction split-centre quotient

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`) define
`[G] = A_G G(F) \ G(A_F)` in (2.20)--(2.21), printed pp. 68--69. In
(6.20)--(6.21), printed p. 168 (PDF p. 182), they define `L²_cusp([G])` as
the `φ ∈ L²([G])` such that, for the unipotent radical `N` of every proper
parabolic `P`, the integral `∫_{[N]} φ(n g) dn` vanishes for almost every `g`.
Lemma 9.2.1, printed p. 242 (PDF p. 254), states that `L²_cusp([G])` is closed.

The published modules `GroupSchemeParabolicL2Period` and
`GroupSchemeFullAEL2` implement this condition on the positive-torus quotient
`PositiveRationalQuotient F G T i`: `fullAEL2CuspidalLocus`, the submodule
`fullAEL2CuspidalSubmodule` and the subrepresentation
`fullAEL2CuspidalSubrepresentation`. The published proof
`groupSchemeParabolicL2Closedness` shows that this locus is closed.

This module defines the same condition directly on the restriction quotient
`RestrictionSplitCentre.Quotient F G S j` of the published
`AdelicRestrictionSplitCentre`, which has the GH shape `A_G G(F) \ G(A_F)`.
It then uses the published identification `quotientL2Equiv` of
`GroupSchemeRestrictionQuotientL2` to prove that the condition defines a
closed subspace stable under right translation, isometrically isomorphic to
the published positive-torus subspace.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `hPD : ParabolicDynamicStatement` and `hG : IsConnectedReductive G` are the
  published hypotheses that supply the proper rational parabolics
  `ProperRationalParabolic G` and their radicals
  `properRationalParabolicRadicals hPD hG P`.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction `AffineWeil.groupScheme ℚ F G`.
- From the section `Transport` on: a commutative group scheme `T` over `F`,
  a map `i : T ⟶ G`, and `h : subgroup F G S j = imageSubgroup F T G i`. The
  published `comparison` theorem gives `h` whenever `j` and `i` are split
  components.
- For the subspace: `hi`, injectivity of `characterRestrict i`, finite index
  of its range, `hc : IsCentral i` and `hT : IsSplitTorus T`. Closedness and
  the right action also assume that Haar measure on the norm-one subgroup
  `G(A_F)^1` is right invariant, as the published positive-torus results do.

## The condition on the restriction quotient

No hypothesis relating `S, j` to a torus is used here.

- `quotientParabolicPeriodIntegrand F G hPD hG S j P φ g`, for
  `φ : Quotient F G S j → ℂ` and `g` in the norm-one subgroup, is the function
  on `[N_P] = N_P(F) \ N_P(A_F)` given by `[n] ↦ φ([n g])`
  (`quotientParabolicPeriodIntegrand_mk`). It is the published
  `periodIntegrand` with trivial character, applied to `φ` composed with the
  published `normOneToQuotient`. This is the pattern of the published
  `properParabolicPositivePeriodIntegrand`.
- `HasConvergentQuotientParabolicPeriod` says that this integrand is
  integrable for the published mass-one measure
  `properParabolicQuotientMeasure F G hPD hG P` on `[N_P]`.
  `quotientParabolicPeriod` is its integral.
- `IsAEQuotientParabolicCuspidal F G hPD hG S j φ`: for every proper
  rational parabolic `P`, the integral converges for almost every `g` and
  vanishes for almost every `g`, both for Haar measure on the norm-one
  subgroup.
- `quotientFullAEL2CuspidalLocus F G hPD hG S j measureQ` is the set of
  `L²` classes, for a measure `measureQ` on the quotient, whose chosen
  representative satisfies `IsAEQuotientParabolicCuspidal`.

## Transport to the positive-torus quotient

Assume `h`. Write `E` for the published `quotientMeasurableEquiv F G h`, the
identity on representatives from `PositiveRationalQuotient F G T i` to
`Quotient F G S j`.

- `quotientParabolicPeriodIntegrand_eq`: the integrand of `φ` equals the
  published positive-torus integrand of `φ ∘ E`. The proof is the published
  identity `E ∘ normOneToPositiveQuotient = normOneToQuotient`
  (`quotientMeasurableEquiv_normOneToPositiveQuotient`).
- `hasConvergentQuotientParabolicPeriod_iff` and `quotientParabolicPeriod_eq`
  follow, and `isAEQuotientParabolicCuspidal_iff` says that `φ` satisfies the
  condition exactly when `φ ∘ E` lies in the published
  `aeParabolicCuspidalFunctionSubmodule`.
- `mem_quotientFullAEL2CuspidalLocus_iff`, with explicit `I`, `e` and `hc`
  as in the published module: for the canonical measure
  `quotientHaarMeasure F G S j`, a class `φ` lies in the locus if and only if
  `(quotientL2Equiv F G h).symm φ` lies in the published
  `fullAEL2CuspidalLocus`. The representative of
  `(quotientL2Equiv F G h).symm φ` agrees almost everywhere with `φ ∘ E`
  (`coeFn_quotientL2Equiv_symm`), and the published
  `mem_aeParabolicCuspidalFunctionSubmodule_congr` shows that the condition
  does not change under such agreement.
- `quotientFullAEL2CuspidalLocus_eq_preimage` states the same as an
  equality of sets, and `mem_quotientFullAEL2CuspidalLocus_iff_of_splitTorus`
  takes `hT` in place of `I` and `e`.

## The subspace and its right action

All of these use the canonical measure `quotientHaarMeasure F G S j`.

- `quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT` is the complex
  subspace whose carrier is the locus itself
  (`mem_quotientFullAEL2CuspidalSubmodule`). Closure under zero, addition and
  scalars comes from the published `fullAEL2CuspidalSubmodule` through
  `mem_quotientFullAEL2CuspidalLocus_iff`.
- `isClosed_quotientFullAEL2CuspidalLocus` and
  `isClosed_quotientFullAEL2CuspidalSubmodule`: the locus is closed. It is
  the preimage of the published locus under the continuous map
  `(quotientL2Equiv F G h).symm`, and the published
  `groupSchemeParabolicL2Closedness` shows that the published locus is
  closed. `completeSpace_quotientFullAEL2CuspidalSubmodule` follows, so the
  subspace is a Hilbert space.
- `quotientFullAEL2CuspidalSubrepresentation F G hPD hG h hi hc hT hInv'`,
  for any `hInv'` saying that the canonical measure is right invariant, is
  the subspace as a subrepresentation of the published right regular
  representation `rationalQuotientL2RightAction`. Stability is the published
  stability of `fullAEL2CuspidalSubrepresentation`, transported by the
  published intertwining property `quotientL2Equiv_rightAction`.
- `quotientFullAEL2CuspidalRightAction` is the restricted representation,
  `norm_quotientFullAEL2CuspidalRightAction` states that it preserves norms,
  and `quotientFullAEL2CuspidalToLp` is the inclusion as an intertwining map.

## Comparison with the positive-torus subspace

- `fullAEL2CuspidalEquiv F G hPD hG h hi I e hc` is the restriction of
  `quotientL2Equiv F G h` to an isometric linear isomorphism from the
  published `fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` onto
  `quotientFullAEL2CuspidalSubmodule`. `coe_fullAEL2CuspidalEquiv` records
  that it is `quotientL2Equiv` on underlying classes.
- `fullAEL2CuspidalEquiv_rightAction`: it intertwines the published
  `fullAEL2CuspidalRightAction` with `quotientFullAEL2CuspidalRightAction`.

## Independence of the auxiliary torus

`quotientFullAEL2CuspidalSubmodule_eq`: the subspaces built from two choices
`(T, i)` and `(T', i')` coincide, since both have the intrinsic locus as
carrier.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`, injectivity
of `characterRestrict i` and finite index of its range. The published
`subgroup_eq_of_splitComponents` supplies `h`, and `hs` supplies `hc` and
`hT`.

- `splitComponentFullAEL2CuspidalSubmodule` is the subspace;
  `mem_splitComponentFullAEL2CuspidalSubmodule` states that its carrier is the
  locus.
- `mem_splitComponentFullAEL2CuspidalSubmodule_iff`: the published
  `splitComponentL2Equiv` maps the published positive-torus locus onto it.
- `isClosed_splitComponentFullAEL2CuspidalSubmodule`: it is closed.
- `splitComponentFullAEL2CuspidalSubrepresentation` is the subspace as a
  subrepresentation of the published `splitComponentL2RightAction`.

## Scope and what is not claimed

- The almost-everywhere variable is the norm-one subgroup `G(A_F)^1` with
  its Haar measure, as in the published positive-torus locus. GH quantify
  over `A_G \ G(A_F)` with a Haar measure. The published
  `splitComponentNormOneDecomposition` writes `G(A_F)` as the product of the
  positive torus image and `G(A_F)^1`, under its own explicit hypotheses.
  This module does not use it and does not prove that the two
  almost-everywhere conditions agree.
- The measure on `[N_P]` is the published mass-one quotient measure. GH use
  a Haar measure; a positive scalar does not affect convergence or
  vanishing.
- The condition applies to the chosen representative of an `L²` class.
  Independence of the representative is proved only for the canonical
  measure `quotientHaarMeasure F G S j`, through `h`.
- The subspace, its closedness and its right action require `h`, injectivity
  and finite index of `characterRestrict i`, centrality and splitness of `i`,
  and right invariance of norm-one Haar measure. These are not proved for
  general data here; for split components the comparison theorem supplies
  `h`.
- Nothing here relates this subspace to continuous or smooth cusp forms, to
  density of any space of forms, or to discreteness or trace-class
  properties of the cuspidal spectrum (GH Theorem 9.1.2).

## Provenance

This is an internal construction. The intrinsic definitions follow the
published positive-torus definitions with the restriction quotient in place
of the positive-torus quotient. Every theorem transports a published result
along the published identification of the two quotients. No new external
theorem is asserted; GH (6.20)--(6.21) and Lemma 9.2.1 are cited for the
definition being implemented and for the closedness that the published proof
supplies.
