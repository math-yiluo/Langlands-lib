# Separation by unitary Satake parameters

Module `Langlands.Representation.RankinSelberg.HighlyRamified.UnitarySeparation`.

## Statements

- `unitCircle_infinite`: the set `{z ∈ ℂ | ‖z‖ = 1}` is infinite.
- `torusPolynomial_eq_zero_of_unit_evaluations σ p`: an element `p` of the Laurent
  polynomial algebra `TorusPolynomialAlgebra σ ℂ` (finite variable type `σ`) whose
  evaluation `torusPolynomialEvaluation σ ℂ x p` vanishes at every unit tuple `x` with
  `‖x i‖ = 1` for all `i` is zero.
- `symmetricTorus_eq_zero_of_unit_evaluations σ p`: the same for elements of the symmetric
  Laurent subalgebra and `symmetricTorusEvaluation`.
- `degreeCorankOneModelCoefficient_eq_zero_of_unit_integrals_eq_zero h π hπ ℓ w hzero d`:
  for a Jacquet normalization `h : IsJacquetNormalization q ψ abv ϖ μ`, a smooth
  representation `π` of `GL_(n+2)(F)`, a `ψ`-Whittaker functional `ℓ` and a model vector
  `w`, suppose that for every tuple `x : Fin (n+1) → ℂˣ` with all `‖x i‖ = 1` there is a
  real `a` such that for every real `s > a` the corank-one integral of `w` against
  `inverseSphericalWhittaker h.conductor.1 h.uniformizer q x` converges and vanishes. Then
  every Laurent degree coefficient `degreeCorankOneModelCoefficient h π hπ ℓ w d` is zero.
- `eq_zero_on_restriction_of_unit_integrals_eq_zero`: under the same hypothesis and
  `IsIntegralInvariantOnRestriction π ℓ w` (right `GL_(n+1)(O)`-invariance on
  `diag(GL_(n+1), 1)`), `w` vanishes on `diag(g, 1)` for every `g ∈ GL_(n+1)(F)`.
- `eq_zero_on_mirabolic_of_unit_integrals_eq_zero`: under the same hypotheses `w`
  vanishes on the mirabolic subgroup.

These are variants of the Library theorems
`Conductor.symmetricTorus_eq_of_evaluations`,
`Conductor.degreeCorankOneModelCoefficient_eq_zero_of_integrals_eq_zero` and
`Conductor.eq_zero_on_restriction_of_integrals_eq_zero`, whose hypotheses quantify over all
Satake parameters `x`; here only unitary parameters are required.

## Proofs

- The unit circle contains the image of `[0, 1]` under `θ ↦ exp(iθ)` (Mathlib's
  `Circle.exp`), which is injective on `[0, 1]` because `1 < 2π`
  (`Circle.exp_injOn_Icc`, `Real.two_le_pi`); the interval is infinite.
- For the Laurent polynomial, write `p = a / (∏ X_i)^m` with `a` a polynomial
  (`IsLocalization.Away.surj`). Evaluating at unit tuples shows that the polynomial `a`
  vanishes on the product of unit circles, so `a = 0` by Mathlib's
  `MvPolynomial.funext_set` (a polynomial vanishing on a product of infinite sets is
  zero); hence `p = 0` because `∏ X_i` is a unit. This is the proof of the Library's
  `Conductor.torusPolynomial_eq_zero_of_evaluations` with the sets `ℂ \ {0}` replaced by
  the unit circle.
- The degree-coefficient statement repeats the proof of the Library theorem
  `Conductor.degreeCorankOneModelCoefficient_eq_zero_of_integrals_eq_zero` verbatim,
  replacing the final separation step by `symmetricTorus_eq_zero_of_unit_evaluations`: for
  a unitary `x`, the evaluated degree coefficients vanish below some degree
  (`degreeCorankOneModelCoefficient_eq_zero_below`), their generating series is the
  corank-one integral at `X = q^(-s)` (`hasSum_corankOneIntegral`,
  `symmetricTorusEvaluation_degreeCorankOneModelCoefficient`), which vanishes for all
  small `X > 0`, so all coefficients vanish (`eq_zero_of_hasSum_int_eq_zero`).
- The restriction statement then follows from the Library separation theorem
  `Conductor.eq_zero_on_restriction_of_degreeCoefficients_eq_zero`, and the mirabolic
  statement from `Conductor.whittaker_mirabolic_eq_of_levi_eq` applied to `w` and `0`.

## Use

In the proof of the level of the zero-cell Kirillov lift (JPSS 1981, proof of Theorem
(5.1)(ii), specialized to `L(s, π) = 1`), the test representations are unitary unramified
principal series, whose irreducibility and genericity are available for unitary Satake
parameters; these lemmas let the separation argument use only those test
representations.
