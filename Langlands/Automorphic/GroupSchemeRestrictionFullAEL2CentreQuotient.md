# The almost-everywhere cuspidal condition over `A_G \ G(A_F)`

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`), (6.20)--(6.21),
printed p. 168, define `L²_cusp([G])` for `[G] = A_G G(F) \ G(A_F)`. A class
`φ` is cuspidal when, for the unipotent radical `N` of every proper parabolic
`P < G`, `∫_{[N]} φ(n g) dn = 0` "for almost every `g ∈ A_G \ G(A_F)` with
respect to a Haar measure on `A_G \ G(A_F)`".

The published module `GroupSchemeRestrictionFullAEL2` states a related
condition, `IsAEQuotientParabolicCuspidal`, on the restriction quotient
`Quotient F G S j`, with the almost-everywhere quantifier over the norm-one
subgroup `G(A_F)^1`. The published module `GroupSchemeRestrictionFullAEL2FullGroup`
states it over the whole group `G(A_F)`, as `IsAEQuotientFullParabolicCuspidal`.
This module builds the quotient group `A_G \ G(A_F)` with its Borel
σ-algebra. It states the condition there, with the quantifier for Haar measure
on that quotient, as GH write it. Under the published decomposition
hypotheses it proves that the three conditions agree.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `hPD : ParabolicDynamicStatement` and `hG : IsConnectedReductive G` are
  the explicit hypotheses of the published proper-parabolic radicals.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction `AffineWeil.groupScheme ℚ F G`. The published
  `subgroup F G S j` is the image of its positive points in `G(A_F)`; it
  plays the role of `A_G`.
- From the quotient on: an instance `(subgroup F G S j).Normal`.
- From the cuspidal section on:
  `hZ : subgroup F G S j ≤ Subgroup.center (AdelicGroupPoints F G)`.
- In the Haar and comparison sections: a commutative group scheme `T` over
  `F` and `i : T.toGrp ⟶ G` with the following hypotheses.
  - `hi`: `characterRestrict i` is injective.
  - The range of `characterRestrict i` has finite index.
  - `hc : IsCentral i`.
  - Either splitting coordinates
    `e : T.toGrp ≅ splitTorus (Spec F) I` with `I` finite, or
    `hT : IsSplitTorus T.toGrp`.
  - `h : subgroup F G S j = imageSubgroup F T G i`. For split components
    `j` and `i`, the published comparison theorem supplies it.

## Centrality

- `subgroup_le_center_of_splitting` (uses `hc` and `h`): the split-centre
  image is central. It is the image of the positive points of `T`, and these
  commute with every adelic point by the published `positivePointMap_commute`.
  So `hZ` follows from `hc` and `h`.
- `positivePointMap_mem_subgroup` (uses `h`): each `positivePointMap a` lies
  in `subgroup F G S j`.
- `commute_of_le_center` (uses `hZ`): each point of the image commutes with
  every adelic point.
- `normal_of_le_center` (uses `hZ`): a central image is normal. It supplies
  the instance needed below, for example with `haveI`.

## The quotient `A_G \ G(A_F)`

- `CentreQuotient F G S j` is the quotient group
  `AdelicGroupPoints F G ⧸ subgroup F G S j`. It carries Mathlib's quotient
  group structure, quotient topology, topological group structure and local
  compactness.
- Its σ-algebra is the Borel σ-algebra of the quotient topology, with
  `BorelSpace`. Mathlib's own instance on a quotient group is the quotient
  σ-algebra, which is not known here to be the Borel one. The Borel choice
  makes Haar measures on `A_G \ G(A_F)` Borel measures in the usual sense.
- `CentreQuotient.mk` is the quotient homomorphism, with `mk_surjective`,
  `continuous_mk`, and `mk_mul_of_mem`: `mk (z * g) = mk g` for `z` in the
  image.
- `CentreQuotient.lift f hf` turns a function `f` on `G(A_F)` with
  `f (z * g) = f g` for `z` in the image into a function on the quotient.
  `lift_mk` holds by definition.
- `CentreQuotient.ae_eq_ae_haar`: every regular Haar measure `ν` on the
  quotient has the same almost-everywhere filter as Mathlib's
  `Measure.haar`. By Mathlib's `isMulLeftInvariant_eq_smul_of_regular`, `ν`
  is a positive multiple of `Measure.haar`.

## Haar measure under the decomposition hypotheses

These results use `hi`, the finite-index hypothesis, `e`, `hc` and `h`.

- `normOneCentreQuotientEquiv` is an isomorphism of topological groups
  `G(A_F)^1 ≃ₜ* A_G \ G(A_F)`. It sends a norm-one point `n` to `mk n`. Its
  inverse lifts the published continuous projection `normOneProjection`,
  which kills the positive points by `normOneProjection_positivePointMap`.
  The published `normOneProjection_normOne` gives one inverse law. The
  published factorization `positivePointMap_mul_normOneFactor` gives the
  other, since `mk` kills the positive factor.
- `CentreQuotient.ae_haar_iff_ae_normOne`: a property `p` of the quotient
  holds Haar-almost everywhere on `A_G \ G(A_F)` exactly when `p (mk m)`
  holds Haar-almost everywhere on `G(A_F)^1`. The pushforward of Haar
  measure on `G(A_F)^1` along the isomorphism is a regular Haar measure.
  So Haar measure on the quotient is a positive multiple of it. The
  isomorphism is a measurable embedding, so Mathlib's `ae_map_iff` applies.
- `CentreQuotient.ae_haar_iff_ae_haar_mk`: the same property holds
  Haar-almost everywhere on the quotient exactly when `p (mk g)` holds
  Haar-almost everywhere on `G(A_F)`. This combines the previous lemma with
  the published `ae_haar_iff_ae_normOne_of_decomposition`, since
  `mk (positivePointMap a * m) = mk m`.

## The cuspidal condition on the quotient

These definitions use `hZ`.

- `centreQuotientParabolicPeriod F G hPD hG S j hZ P φ` lifts the published
  period `quotientFullParabolicPeriod`, `g ↦ ∫_{[N_P]} φ(n g) dn`, to the
  quotient. The published `quotientFullParabolicPeriod_mul` shows that the
  period is invariant under central points of the image.
  `centreQuotientParabolicPeriod_mk` gives its value at `mk g`.
- `HasConvergentCentreQuotientParabolicPeriod` lifts the published
  integrability predicate `HasConvergentQuotientFullParabolicPeriod` in the
  same way, through `quotientFullParabolicPeriodIntegrand_mul`. Both use the
  published mass-one measure on `[N_P]`.
- `IsCentreQuotientParabolicCuspidal F G hPD hG S j hZ φ`: for every
  `P : ProperRationalParabolic G`, the period converges at almost every point
  of `A_G \ G(A_F)`, and it vanishes almost everywhere, both for
  `Measure.haar` on `CentreQuotient F G S j`.
- `isCentreQuotientParabolicCuspidal_iff_of_regular`: the condition is
  unchanged when `Measure.haar` is replaced by any regular Haar measure `ν`
  on the quotient. This matches GH's "a Haar measure" for regular Haar
  measures.

## Comparison with the published conditions

These results use `hZ`, `hi`, the finite-index hypothesis, `hc`, `h`, and
`e` or `hT`.

- `isCentreQuotientParabolicCuspidal_iff_full_of_splitting`: the condition on
  the quotient holds exactly when the published full-group condition
  `IsAEQuotientFullParabolicCuspidal φ` holds. Apply
  `ae_haar_iff_ae_haar_mk` to the convergence clause and to the vanishing
  clause.
- `isCentreQuotientParabolicCuspidal_iff_of_splitting`: it holds exactly when
  the published norm-one condition `IsAEQuotientParabolicCuspidal φ` holds,
  by the published `isAEQuotientFullParabolicCuspidal_iff_of_splitting`.
- `isCentreQuotientParabolicCuspidal_iff` is the same statement, with the
  splitting obtained from `hT`.
- `mem_quotientFullAEL2CuspidalLocus_iff_centreQuotient`: for every measure
  on `Quotient F G S j`, an `L²` class lies in the published locus
  `quotientFullAEL2CuspidalLocus` exactly when its representative satisfies
  the condition on `A_G \ G(A_F)`.

## Provenance and scope

All proofs are internal combinations of published Library results and
Mathlib. The statement on `A_G \ G(A_F)` follows GH (6.21) in the following
respects. The quantifier runs over the quotient by the split-centre image,
for a Haar measure there, with the Borel σ-algebra. Two features are
published conventions rather than GH text. The parabolics range over the
published `ProperRationalParabolic G`. The convergence clause is part of the
published condition; (6.21) writes only the vanishing of the integral.

The listed hypotheses are sufficient for the comparisons; necessity is not
claimed. `isCentreQuotientParabolicCuspidal_iff_of_regular` covers regular
Haar measures only. Haar measures that are not regular are not treated.
Without the decomposition hypotheses, the module only defines the quotient
condition and compares Haar measures on the quotient. The comparison
hypotheses are not proved here for general data: for split components the
comparison theorem gives `h`, and injectivity of `characterRestrict i` is
currently derived from the unproved central split torus statement.
