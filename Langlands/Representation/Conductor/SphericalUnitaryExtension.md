# The spherical corank-one functional equation: from unitary to all Satake parameters

This internal unit is a step towards the published
`SphericalLaurentFunctionalEquationStatement`. It shows that the normalized
functional equation for the corank-one integrals against spherical Whittaker
functions extends from unitary Satake parameters (`|x_i| = 1`) to all parameters
`x : Fin (n + 1) → ℂˣ`. Convergence and the Laurent-polynomial numerators must be
known for every `x`. The unitary case, the convergence and the Laurent numerators are
explicit hypotheses of the final theorem; this unit proves no instance of them.

The final theorem is `normalizedFunctionalEquation_of_unitary`. The other
declarations are algebraic and analytic lemmas for it.

## Setting and notation

`h : IsJacquetNormalization q ψ abv ϖ μ` and
`h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ` are Jacquet's normalizations
for `ψ` and `ψ̄`, over an arbitrary nonarchimedean local field `F`, including positive
characteristic. `π` and `ρ` are smooth representations of `GL_(n+2)(F)` on complex
vector spaces in independent universes. `ℓ` is a `ψ`-Whittaker functional of `π` and
`ℓ'` a `ψ̄`-Whittaker functional of `ρ`. The model vectors are
`w : coefficientModel π ℓ` and `w' : coefficientModel ρ ℓ'`. `P` and `Pd` are complex
polynomials with constant term `1`.

For a tuple of units `x`:

- `W(x; ψ̄)` is `inverseSphericalWhittaker h.conductor.1 h.uniformizer q x` and
  `W(x⁻¹; ψ)` is `inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹`;
- `Ψ(s, w, W(x; ψ̄))` is `corankOneIntegral ψ abv μ w.val W(x; ψ̄) s`, and
  `Ψ(s, w', W(x⁻¹; ψ))` is the same with `ψ.scale (-1)`, `w'` and `W(x⁻¹; ψ)`;
- `X = q^(-s)`, and `essentialFactor P x` is `∏ i, P(x_i X)⁻¹` as a rational function
  of `X`.

## The final theorem

`normalizedFunctionalEquation_of_unitary` assumes, for every `x`:

- `hconv`, `hconvd`: `Ψ(s, w, W(x; ψ̄))` and `Ψ(s, w', W(x⁻¹; ψ))` converge
  (`CorankOneConverges`) for `Re s > a`, for some `a` depending on `x`;
- `hQ`, `hQd`: they have rational continuations (`HasRationalContinuation`)
  `R_x = Q x · ∏ P(x_i X)⁻¹` and `Rd_x = Qd x · ∏ Pd(x_i⁻¹ X)⁻¹`, where `Q x` and
  `Qd x` are Laurent polynomials in `X`.

It also assumes `hunit`: for every `x` with `‖x_i‖ = 1` for all `i`, the published
`NormalizedFunctionalEquation`

`∏ Pd(x_i⁻¹ q^(-(1-s))) Rd_x(q^(-(1-s))) = ζ^e c (∏ x_i)^m q^(-ks) ∏ P(x_i q^(-s)) R_x(q^(-s))`

holds wherever both continuations are defined. Here `ζ, c ∈ ℂˣ`, `e ∈ ℕ` and
`m, k ∈ ℤ` are arbitrary and do not depend on `x`. The conclusion is the same equation
for every `x`. The published statement uses the case `ζ = 1`, `e = n + 1`,
`c := c^(n+1)` and `k = (n + 1) m`.

## Proof

1. **Coefficients of the numerator** (`laurentNumerator_coeff_eq_specialized`).
   The published `corankOneModelDenominatorProduct h π hπ ℓ w P` is Jacquet's formal
   series `Ψ(X; W) ∏ P(X X_i)` (Jacquet 2012, printed page 520): a Laurent series in
   `X` whose coefficients lie in the symmetric Laurent polynomials in the torus
   coordinates `X_i`. It does not depend on `x`. Under `hconv` and `hQ` at `x`, the
   `d`-th coefficient of `Q x` equals the value at `x` of its `d`-th coefficient. On
   real `s` beyond both abscissae, the published `hasSum_specializedDenominatorProduct`
   expresses `∏ P(x_i q^(-s)) Ψ(s, w, W(x; ψ̄))` as the Laurent sum of the specialized
   coefficients. The rational continuation (with `∏ P(x_i X) · R_x = Q x`,
   `laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor`) expresses the same
   value as the finite Laurent sum of `Q x`. Both coefficient families vanish below
   some degree (`corankOneModelDenominatorProduct_coeff_eq_zero_below`). The published
   identity theorem `eq_zero_of_hasSum_int_eq_zero` on an interval `(0, r)` then
   makes the coefficients equal. The points of `(0, r)` are values `q^(-s)` by
   `exists_spectralPoint_eq`.
2. **Dual coefficients.** The same step for `ρ`, `ℓ'`, `w'`, `Pd`, `h'` at `x⁻¹`
   gives the coefficients of `Qd x` as values at `x⁻¹` of fixed Laurent polynomials.
   `torusPolynomialInversion` is the `ℂ`-algebra endomorphism of the Laurent
   coordinate ring `TorusPolynomialAlgebra` sending `X_i` to `X_i⁻¹`. It is built by
   the universal property of the localization at `∏ X_i`, using that each `X_i` is a
   unit (`isUnit_torusCoordinate`, `torusInverseCoordinate`). By
   `torusPolynomialEvaluation_inversion`, evaluating its image at `x` is evaluating
   at `x⁻¹`. So the coefficients of `Qd x` are values at `x` of fixed Laurent
   polynomials as well.
3. **Coefficientwise form of the equation.** Clearing denominators, the functional
   equation at `x` is equivalent to the Laurent identity
   `Qd x (q⁻¹X⁻¹) = ζ^e c (∏ x_i)^m X^k · Q x (X)` (`reflectLaurent`). The published
   `normalizedFE_cleared_laurent_identity` gives one direction;
   `normalizedFunctionalEquation_of_laurent_identity` gives the converse by evaluating
   at `X = q^(-s)`. By `reflectLaurent_coeff` and `monomial_mul_laurent_coeff`, its
   `j`-th coefficient reads
   `q^j (Qd x)_(-j) = ζ^e c (∏ x_i)^m (Q x)_(j-k)`.
4. **Polynomial identity.** By steps 1 and 2, for each `j` the difference of the two
   sides is the value at `x` of a fixed element `E j` of `TorusPolynomialAlgebra`. The
   factor `(∏ x_i)^m` is the value of the `m`-th power of the published
   `torusDeterminantUnit` (`torusPolynomialEvaluation_determinantUnit`). By `hunit`
   and step 3, `E j` vanishes at every unitary `x`. A Laurent polynomial that
   vanishes on the compact torus is zero
   (`torusPolynomial_eq_zero_of_unitary_evaluations`). Write it as
   `(∏ X_i)^(-N) a` with `a` a polynomial. Then `a` vanishes on the product of unit
   circles, which are infinite (`setOf_norm_eq_one_infinite`). Mathlib's
   `MvPolynomial.funext_set` gives `a = 0`. So `E j = 0`, the coefficient identities of
   step 3 hold at every `x`, and step 3 gives the functional equation at every `x`.

## Provenance

The argument is internal: it is the principle of analytic continuation in the
Satake parameters, made algebraic by Jacquet's formal series. The formal series
`Ψ(X; W) ∏ P(X X_i)` and its specializations are from H. Jacquet, *A correction to
Conducteur des représentations du groupe linéaire*, Pacific J. Math. 260 (2012),
515–525 (registered `jacquet-2012-conductor-correction`), printed pages 520–521.
The unitary case of the functional equation is JPSS 1981, (4.2)(3), printed page 209
(H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Conducteur des représentations
du groupe linéaire*, Math. Ann. 256 (1981), 199–214, registered
`jpss-1981-conductor`): for `|x_i| = 1` the principal series `I(x)` is irreducible and
generic. Here that case is the hypothesis `hunit`. The literature obtains the equation
for all `x` directly from JPSS 1983, Theorem (2.7), for representations of Whittaker
type; this unit gives a route from the unitary case instead.

## What it does not assert

It proves neither convergence, rationality, the Laurent-polynomial numerators nor
the unitary functional equation; these are hypotheses. It does not identify the dual
integral `Ψ(s, w', W(x⁻¹; ψ))` with the dual integral of the published statement
(`firstDualFunction`, `secondDualFunction`), nor `ρ` with a contragredient of `π`,
nor `Pd` with an L-polynomial. It does not use irreducibility or genericity of `π` or
`ρ`, only smoothness.

## Imports

The published modules `Conductor.EssentialExistenceReduction` (spherical series,
products and their specializations, `exists_spectralPoint_eq`,
`hasSum_specializedDenominatorProduct`),
`RankinSelberg.TwoBlockFirstBlockLaurentReflection` (`reflectLaurent`,
`normalizedFE_cleared_laurent_identity`) and
`RankinSelberg.BilateralSpectralEvaluation` (`hasSum_ofLaurentPolynomial`), all under
`Langlands.Representation`.
