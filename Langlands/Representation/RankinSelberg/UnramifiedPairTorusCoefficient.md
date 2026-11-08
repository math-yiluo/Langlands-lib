# Torus coefficients of the unramified unequal-rank integrand

Author: Worker 1797. Module
`Langlands.Representation.RankinSelberg.UnramifiedPairTorusCoefficient`, namespace
`Langlands.RankinSelberg.UnramifiedPairTorus`.

This module reduces the actual unequal-rank Rankin–Selberg integral of two normalized
spherical vectors to a series over partitions. The main result is
`pairIntegral_eq_tsum`. Conjunct (B) of `UnramifiedPairStatement` is derived from it in
`UnramifiedPairProof`.

## Source and provenance

The computation is Jacquet–Shalika, *On Euler products and the classification of
automorphic forms II*, Amer. J. Math. 103 (1981), §1.4, printed pp. 780–781 (literature
id `jacquet-shalika-1981-euler-products-ii`). There, the integral
`Ψ(s, W₀, W₀') = ∫ W₀(diag(g, 1_(k+1))) W₀'(g) |det g|^(s - (k+1)/2) dg`
over `N_(n+1) \ GL_(n+1)` is computed with the Iwasawa decomposition, Shintani's formula
for `W₀` on torus elements, and the Cauchy identity. Everything in this module is
internal and derived. The one definition, `extendWeight`, is an auxiliary padding of
exponent vectors and has no counterpart in the source. The analytic regrouping (the
Cauchy identity) is not done here: it is Worker 1767's `exists_schurCauchy_radius`,
applied in `UnramifiedPairProof`.

## Weights

- `extendWeight n d lam : Fin (n + d + 1) → ℤ` extends `lam : Fin (n + 1) → ℤ` by `d`
  zero coordinates. It is literally the exponent in the Library lemma
  `SquareIntegrableWhittakerRestriction.appendIdentity_torus`, i.e.
  `diag(ϖ^lam, 1_d) = ϖ^(extendWeight n d lam)`.
- `padWeight_apply`, `jacobiTrudiIn_cast` and `jacobiTrudiIn_extendWeight`: the
  Jacobi–Trudi determinant of the padded weight in any alphabet equals that of `lam`.
  This comes from the Library's `jacobiTrudiIn_padWeight` after a cast of the index type.
- `isPartitionExponent_of_antitone_extendWeight`: if `extendWeight n (d+1) lam` is
  antitone, then `lam` is antitone and nonnegative, because the padded zero follows
  every coordinate. `antitone_extendWeight` is the converse.
- `sum_mul_extendWeight`: weighted coordinate sums of the padded weight agree with those
  of `lam`.

## Exponent identities

- `prod_zpow_eq_zpow_sum`: `∏ x ^ f i = x ^ ∑ f i` in `ℝ` for `x ≠ 0`.
- `sum_pairs_sub`: `∑_(i<j) (lam_i - lam_j) = ∑_i (n - 2i) lam_i` on `Fin (n + 1)`.

## The zero-dimensional rectangular variable

With `j = 0` rows, `Matrix (Fin 0) (Fin (n + 1)) F` is a subsingleton, so the integrand
does not depend on `x`. `unequalRankIntegrand_zero_rows` records this.
`unequalRankConverges_of_integrable` turns integrability over `μ` of the integrand at
`x = 0` into `UnequalRankConverges` for `μ.prod (Measure.dirac 0)`, via Mathlib's
`Integrable.comp_fst`. `unequalRankIntegral_dirac` shows the iterated integral is the
`μ`-integral of the integrand at `0`.

## The canonical local field

These results use the canonical topology, valuation and local-field structure of `F` as
local instances.

- `appendIdentity_mem_integralSubgroup`: `diag(y, 1_d)` is integral when `y` is. The
  entries are those of `y`, `0` or `1`, and the inverse is `diag(y⁻¹, 1_d)`.
- `unequalRankFunction_mul_integral`: if both Whittaker functions are right invariant
  under the integral groups, then so is the unequal-rank function with no rectangular
  rows. This uses `unequalRankMatrix_zero_rows` and `determinantWeight_mul_integral`.
- `isOpen_integralSubgroup` and `continuous_unequalRankIntegrand`: right invariance
  under the open integral subgroup makes the function locally constant, hence
  continuous (Library `continuous_of_rightInvariant`). It then descends continuously to
  the quotient (`Continuous.quotient_lift`).
- `valuation_eq_of_isUniformizingElement`: two uniformizing elements `ϖ`, `ϖ'` have the
  same valuation. Write `v ϖ' = v ϖ ^ m` and `v ϖ = v ϖ' ^ m'`. Injectivity of
  `m ↦ v ϖ ^ m` gives `m m' = 1`, and `v ϖ' < 1` forces `m > 0`, hence `m = 1`.
- `abv_uniformizerUnit`: Jacquet's normalization (`|ϖ| = q⁻¹`, `abv = 1` on valuation
  units) gives `abv(ϖ₀) = q⁻¹` for the canonical uniformizer `ϖ₀`. Indeed `ϖ₀ / ϖ` is a
  valuation unit.
- `normalizedAbs_uniformizerUnit_div`, `residueCardinality_real_pos` and
  `density_uniformizerUnit`: the inverse modulus weight of the quotient-measure torus
  decomposition at `ϖ₀^lam` is
  `density = q^(∑_(i<j) (lam_i - lam_j)) = q^(∑_i (n - 2i) lam_i)`, with `q` the residue
  cardinality.
- `scalar_identity`: for `q > 0`, `a ∈ ℤ`, `S ∈ ℕ`,
  `q^a · (√q^(-(a + (k+1) S)) · √q^(-a)) · ((q⁻¹)^S)^(s - (k+1)/2) = (q^(-s))^S`.
  It is proved by writing every factor as a complex exponential of a multiple of
  `log q`. Here `√q^(·)` are the two half moduli, `q^a` is the density and the last
  factor is `|det|^(s - (k+1)/2)`.
- `sum_halfModulus_extendWeight`: the half-modulus exponent of the padded weight in rank
  `n + d + 1` is `∑_i (n - 2i) lam_i + d ∑_i lam_i`.
- `satakeSchur_natWeight` and `satakeSchur_extendWeight`: on a natural partition `α`,
  the Library Schur value `satakeSchur (characterValues F χ)` of `α` (respectively of its
  zero padding) is `jacobiTrudiValue (unramifiedClass F χ) α`. This uses
  `satakeSchur_eq_eval_jacobiTrudi` and `jacobiTrudiIn_extendWeight`.
- `abv_det_torus_natWeight`: `abv(det ϖ₀^α) = (q⁻¹)^(∑ α_i)`.

## Torus coefficients

Fix `π`, `σ`, functionals `ℓ`, `ℓ'`, normalized spherical tests `w`, `w'` and `s`, and
let `E = unequalRankIntegrand ψ abv 0 k w w' s 0` on `N_(n+1) \ GL_(n+1)`. The Library's
`torusCoefficient F T ϖ E lam` is `density(lam) · E(N ϖ^lam)`.

- `torusCoefficient_apply`: this equals
  `density(lam) · W₀(ϖ^(extendWeight lam)) · W₀'(ϖ^lam) · |det ϖ^lam|^(s - (k+1)/2)`.
- `torusCoefficient_eq_zero`: if `lam` is not a partition exponent (antitone and
  nonnegative), the coefficient is `0`. In that case the padded weight is not antitone,
  and the Library's `eval_torus_eq_zero_of_not_antitone` (conductor `O`, via
  `standardCharacter_nondegenerate`) makes `W₀` vanish there.
- `torusCoefficient_natWeight`: for an antitone natural tuple `α`, the coefficient equals
  `schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ') (q^(-s)) α`. Both Whittaker
  values come from Worker 1767's published Shintani formulas `sphericalTest_torus_schur`
  and `inverseSphericalTest_torus_schur`: half modulus times `satakeSchur`. The scalar
  factors then combine by `scalar_identity`.

## Main theorem

```lean
theorem Langlands.RankinSelberg.UnramifiedPairTorus.pairIntegral_eq_tsum : ∀ ... , ...
```

Its hypotheses are exactly those of `UnramifiedPairIntegralStatement`: a prime `p`, a
p-adic field `F`, `n`, `k`, both unramified generic constituents, `q`, `ψ`, `abv`, `ϖ`,
the quotient measure `μ` with `IsJacquetNormalization q ψ abv ϖ μ`, nonzero `ℓ`, `ℓ'`,
and normalized spherical tests `w`, `w'`. It adds `s : ℂ` and the hypothesis that the
norms of `schurPairTerm (unramifiedClass F χ) (unramifiedClass F χ') ((q : ℂ)^(-s)) α`
are summable over `{α : Fin (n + 1) → ℕ // Antitone α}`. It concludes:

- `UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) w w' s`, and
- `unequalRankModelIntegral ψ abv 0 k μ (Measure.dirac 0) π σ ℓ ℓ' w w' s` equals the
  sum of these Schur pair terms.

Proof:

1. Jacquet's normalization gives `q =` the residue cardinality (substituted), conductor
   `O` for `ψ`, and `abv(ϖ₀) = q⁻¹`.
2. The integrand `E` is measurable (continuous) and right invariant on each `K`-fiber.
3. The map `ι α = (α_i : ℤ)` from antitone natural tuples is injective. Off its range
   the coefficients vanish (`torusCoefficient_eq_zero`); on it they are the Schur pair
   terms (`torusCoefficient_natWeight`). So the hypothesis gives summability of all
   coefficient norms (`Function.Injective.summable_iff`).
4. The Library's `integrable_integral_eq_tsum_torus`, applied with the canonical
   uniformizer and the compatible measure `hJ.measure`, gives integrability of `E` and
   `∫ E dμ = ∑' lam, torusCoefficient lam`.
5. The Dirac reduction lemmas turn this into the stated convergence and integral, and
   `Function.Injective.tsum_eq` restricts the sum to partitions.
