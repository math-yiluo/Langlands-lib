# The almost-everywhere cuspidal condition over the full adelic group

Author: Worker 112.

Getz--Hahn (`getz-hahn-2024-automorphic-representations`), (6.20)--(6.21),
printed p. 168, define `L²_cusp([G])` for `[G] = A_G G(F) \ G(A_F)`. A class
is cuspidal when, for the unipotent radical `N` of every proper parabolic,
`∫_{[N]} φ(n g) dn` vanishes for almost every `g` in `A_G \ G(A_F)`, for a
Haar measure there.

The published module `GroupSchemeRestrictionFullAEL2` implements a related
condition, `IsAEQuotientParabolicCuspidal`, on the restriction quotient
`Quotient F G S j`. It quantifies over the norm-one subgroup `G(A_F)^1` with
its Haar measure, and its Markdown states that agreement with the GH
quantifier is not proved. This module states the condition over the whole
group `G(A_F)` with its Haar measure. It proves that the period is invariant
under the split-centre image, and that the full-group and norm-one
conditions agree under the published decomposition hypotheses.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `hPD : ParabolicDynamicStatement` and `hG : IsConnectedReductive G` are
  the explicit hypotheses of the published proper-parabolic radicals.
- `S` is a commutative group scheme over `ℚ` and `j` maps it into the Weil
  restriction `AffineWeil.groupScheme ℚ F G`.
- From the comparison section on: a commutative group scheme `T` over `F`
  and `i : T.toGrp ⟶ G` with the following hypotheses.
  - `hi`: `characterRestrict i` is injective.
  - The range of `characterRestrict i` has finite index.
  - `hc : IsCentral i`.
  - Either splitting coordinates
    `e : T.toGrp ≅ splitTorus (Spec F) I` with `I` finite, or
    `hT : IsSplitTorus T.toGrp`.
  - `h : subgroup F G S j = imageSubgroup F T G i`. For split components
    `j` and `i`, the published comparison theorem supplies it.

## The period at an arbitrary adelic point

- `properParabolicAmbientInclusion F G hPD hG P` is the inclusion of the
  adelic points of the radical of `P` into `G(A_F)`. It is the published
  inclusion into `G(A_F)^1` followed by the subgroup inclusion.
- `properParabolicAmbientInclusion_rational_mem`: rational points of the
  radical land in `A_G G(F)`, through the principal points.
- `quotientFullParabolicPeriodIntegrand F G hPD hG S j P φ g`, for `g` in
  `G(A_F)`, is the published generic `periodIntegrand` with trivial
  character. By `quotientFullParabolicPeriodIntegrand_mk` its value at the
  class of `n` is `φ([n * g])`.
- `HasConvergentQuotientFullParabolicPeriod` is its integrability, and
  `quotientFullParabolicPeriod` its total Bochner integral. Both use the
  published mass-one measure `properParabolicQuotientMeasure`, as the
  norm-one version does.
- `IsAEQuotientFullParabolicCuspidal F G hPD hG S j φ`: for every proper
  rational parabolic `P`, the period converges for almost every `g` in
  `G(A_F)` and vanishes almost everywhere, for `Measure.haar` on
  `AdelicGroupPoints F G`.

## Basic properties

- `quotientFullParabolicPeriodIntegrand_normOne`: at a norm-one point `m`,
  the integrand equals the published `quotientParabolicPeriodIntegrand` at
  `m`. Both send the class of `n` to `φ([n * m])`.
  `hasConvergentQuotientFullParabolicPeriod_normOne` and
  `quotientFullParabolicPeriod_normOne` follow.
- `quotientFullParabolicPeriodIntegrand_mul` and
  `quotientFullParabolicPeriod_mul`: let `z` lie in `subgroup F G S j` and
  commute with every adelic point. Then the integrand and the period at
  `z * g` equal those at `g`. The proof rewrites `n * (z * g)` as
  `z * (n * g)` and uses that `z` lies in `A_G G(F)`. So, for such `z`, the
  period is a function on `A_G \ G(A_F)`.

## Comparison with the norm-one condition

- `ae_haar_iff_ae_normOne_of_decomposition` (uses `hi`, `e` and `hc`). Let
  `p` be a property of adelic points and `q` one of norm-one points, with
  `p (positivePointMap a * m) ↔ q m` for every positive point `a` and
  norm-one point `m`. Then `p` holds Haar-almost everywhere on `G(A_F)`
  exactly when `q` holds Haar-almost everywhere on `G(A_F)^1`.

  The proof uses the published `measurePreserving_normOneDecomposition_symm`.
  The inverse of the multiplication homeomorphism
  `intrinsicSubgroup F T × G(A_F)^1 → G(A_F)` carries Haar measure to the
  product of the published normalized positive Haar measure and norm-one
  Haar measure. The exceptional set of `p` is the preimage of
  `univ ×ˢ {m | ¬ q m}`. Mathlib's `Measure.prod_prod` gives its measure as
  a product. The positive factor has nonzero total mass, because it is a
  Haar measure.
- `isAEQuotientFullParabolicCuspidal_iff_of_splitting` (uses `hi`, `e`, `hc`
  and `h`): `IsAEQuotientFullParabolicCuspidal φ` holds exactly when the
  published `IsAEQuotientParabolicCuspidal φ` holds, for every function `φ`
  on `Quotient F G S j`.

  By `h`, each `positivePointMap a` lies in `subgroup F G S j`. By the
  published `positivePointMap_commute`, it commutes with every adelic point.
  The integrand at `positivePointMap a * m` is therefore the norm-one
  integrand at `m`. The previous lemma is applied to the convergence clause
  and to the vanishing clause separately.
- `isAEQuotientFullParabolicCuspidal_iff` is the same statement, with the
  splitting obtained from `hT`.
- `mem_quotientFullAEL2CuspidalLocus_iff_full`: for every measure on the
  quotient, an `L²` class lies in the published locus
  `quotientFullAEL2CuspidalLocus` exactly when its representative satisfies
  the full-group condition.

## Provenance and scope

All proofs are internal combinations of published Library results and
Mathlib. The full-group condition is stated on representatives in `G(A_F)`
of points of `A_G \ G(A_F)`. The invariance lemma shows that the period is
constant on the cosets of central points of the split-centre image.

This module does not construct a Haar measure on `A_G \ G(A_F)` or prove that
its null sets correspond to the `A_G`-invariant Haar-null sets of `G(A_F)`.
That last identification with the literal GH formulation remains open. The
measure on `[N_P]` is the published mass-one measure. The comparison
hypotheses are not proved here for general data: for split components the
comparison theorem gives `h`. Injectivity of `characterRestrict i` is
currently derived from the unproved central split torus statement.
