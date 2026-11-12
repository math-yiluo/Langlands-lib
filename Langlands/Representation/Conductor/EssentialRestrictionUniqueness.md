# Essential vectors agree on the mirabolic subgroup

This internal unit proves that two essential vectors of the same Whittaker model
agree on the mirabolic subgroup of `GL_(n+2)(F)`, over every nonarchimedean local
field `F`. It is the analytic part of the uniqueness clause of Jacquet 2012,
Theorem 1 (printed page 517). That clause asserts uniqueness of the essential vector,
and Jacquet attributes it to Jacquet, Piatetski-Shapiro and Shalika 1981. Full
uniqueness additionally needs the injectivity of the restriction of the Whittaker
model of a generic representation to the mirabolic subgroup; this unit neither
proves nor assumes that injectivity. It also does not assert existence of an
essential vector or of the L-polynomial.

The essential vector is the published `IsEssentialVector h π ℓ w` of
`Conductor/Essential`: for one standard L-polynomial `P`, every corank-one integral
against `W(g; x; ψ̄)` converges on a right half-plane and continues to
`∏ i, P(x_i X)⁻¹`, and the restriction to `diag(GL_(n+1), 1)` is right
`GL_(n+1)(O)`-invariant.

## Laurent series vanishing on an interval

These results concern complex coefficient sequences only.

- `coeff_zero_eq_zero_of_hasSum_eq_zero`: let `a : ℕ → ℂ` and `r > 0`. If
  `∑ₖ a k X^k` has sum `0` for every real `X` with `0 < X < r`, then `a 0 = 0`.
  The proof uses absolute summability at `r₀ = r / 2`, which holds because unconditional
  summability in `ℂ` implies summability of the norms (`summable_norm_iff`). For
  `0 < X < r₀` this gives `‖a 0‖ ≤ (X / r₀) T` with
  `T = ∑ₖ ‖a (k+1)‖ r₀^(k+1)`. Letting `X → 0⁺` gives `a 0 = 0`.
- `eq_zero_of_hasSum_eq_zero`: under the same hypothesis every `a k` is zero. The
  proof is induction on `k`: once `a 0 = 0`, the shifted sequence `a (k + 1)` satisfies
  the same hypothesis after division by `X`.
- `eq_zero_of_hasSum_int_eq_zero`: let `c : ℤ → ℂ` vanish below some `d₀`. If
  `∑_d c d X^d` has sum `0` for every real `X` in `(0, r)`, then `c` is zero. The
  sum over `ℤ` is transported to the sum over `ℕ` along `k ↦ d₀ + k`, which contains
  the support, and then divided by `X^d₀`.

## Degree strata

- `isOpen_quotientExponent_preimage`: every set of Iwasawa exponents has an open
  preimage in `N_(n+1) \ GL_(n+1)`, being a union of the open cells `sphericalCell`
  (published in `Conductor/SphericalSeparation`).
- `sphericalDegreeStratum hϖ d` is the degree-`d` stratum
  `{t | sphericalQuotientDegree hϖ t = d}` of the quotient
  (`mem_sphericalDegreeStratum_iff`). `isOpen_sphericalDegreeStratum`: each stratum
  is open, being the preimage of the exponents with entry sum `d`.

## The analytic bridge

Fix Jacquet's normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`.

- `corankOneIntegrand_eq_spectralPoint_zpow`: for every pair of Whittaker functions
  and every `s`, the published corank-one integrand at `s` equals
  `spectralPoint q s ^ d` times the integrand at `0`, where
  `spectralPoint q s = q^(-s)` and `d` is the degree of the point. It splits
  `|det g|^(s - 1/2) = |det g|^s |det g|^(-1/2)` and uses the published
  `determinantWeight_eq_degree_power`, with `q > 0` from `IsJacquetNormalization.one_lt_q`.
- `hasSum_corankOneIntegral` (analytic bridge): if the corank-one integral converges
  absolutely at `s` (`CorankOneConverges`), then
  `corankOneIntegral = ∑_d q^(-ds) · ∫ (degree-d part of the integrand at 0) dμ`,
  as an unconditional sum over `d ∈ ℤ`. The proof applies countable additivity of the
  integral (`hasSum_integral_iUnion`) to the open, disjoint degree strata, which cover
  the quotient.
- `degreeCorankOneModelCoefficient_eq_zero_of_integrals_eq_zero`: let `π` be smooth
  and `w` a vector of the model of `ℓ`. Suppose that for every Satake parameter `x`
  there is a real `a` such that for every real `s > a` the corank-one integral of `w`
  against `W(g; x; ψ̄)` converges absolutely and vanishes. Then every Laurent degree
  coefficient `degreeCorankOneModelCoefficient h π hπ ℓ w d` is zero. For each `x`,
  the evaluations of these coefficients at `x` are the degree integrals
  (`symmetricTorusEvaluation_degreeCorankOneModelCoefficient`). They vanish below a
  common degree (`degreeCorankOneModelCoefficient_eq_zero_below`). For
  `0 < X < q^(-a)` put `s = -log X / log q`, so that `s > a` and `q^(-s) = X`. The
  bridge gives `∑_d c_d(x) X^d = 0`, and the Laurent lemma gives `c_d(x) = 0`.
  Separation by evaluations (`symmetricTorus_eq_of_evaluations`) concludes.
- `eq_zero_on_restriction_of_integrals_eq_zero`: under the same hypothesis and
  restriction invariance, `w(diag(g, 1)) = 0` for all `g`. This combines the
  previous result with `eq_zero_on_restriction_of_degreeCoefficients_eq_zero` from
  `Conductor/SphericalSeparation`.

## Essential vectors

- `IsEssentialVector.sub_integrals_eq_zero`: suppose `w₁` and `w₂` are essential
  vectors in the model of `ℓ`. By `IsEssentialVector.satisfiesEssentialIdentity` both
  satisfy the identity with the same polynomial `P`. For every `x`, on a common real
  half-line both integrals converge and equal the value of `essentialFactor P x` at
  `q^(-s)`. So the integral of `w₁ - w₂` converges and vanishes there, by
  `CorankOneConverges.sub` and `corankOneIntegral_sub`.
- `IsEssentialVector.eq_on_restriction`: if `π` is smooth, two essential vectors
  agree on `diag(GL_(n+1), 1)`. The difference is restriction invariant, so the
  previous results apply to it.
- `IsEssentialVector.eq_on_mirabolic`: if `π` is smooth, two essential vectors agree
  at every element of the mirabolic subgroup `mirabolic (n + 1) F` of `GL_(n+2)`. This
  is the published `whittaker_mirabolic_eq_of_levi_eq` applied to the previous result.
