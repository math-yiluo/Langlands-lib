# The dual comparison of essential vectors from the spherical functional equation

Author: Worker 5008.

This module proves the analytic input of the published reduction
`Langlands.Conductor.dualComparison_of_unit_spherical_integrals`: the proportionality of
two families of corank-one integrals against unitary spherical Whittaker functions. It
derives that input from the published statement
`Langlands.Conductor.SphericalCorankOneFunctionalEquationStatement`. With the published
`Langlands.Whittaker.MirabolicRestrictionInjectivityStatement`, it then gives the published
`Langlands.Conductor.EssentialDualComparisonStatement`.

Both of these statements are hypotheses here and neither is proved yet. The final theorem
is an implication between published statements. It is not an unconditional proof of the
dual comparison. Everything holds over an arbitrary nonarchimedean local field, in any
characteristic. The field and vector-space universes are independent.

## Mathematical source

The argument is the first paragraph of the proof in Jacquet, Piatetski-Shapiro and Shalika,
*Conducteur des représentations du groupe linéaire*, Math. Ann. 256 (1981), (5.3), printed
page 213. Let `W` be the essential vector of `π`, `W'` the essential vector of the dual
model, and `W₁(g) = W'(g a)` with `a = diag(ϖ^m, ..., ϖ^m, 1)`.

The identity (4.2)(1) (printed page 208) evaluates the series of `W̃` as
`c^(r-1) q^(-m(r-1)) X^(-m(r-1)) ∏ Xᵢ^(-m) ∏ 1/P̃(X Xᵢ)`. The series of `W₁` has the same
shape. So there is a constant `C'` with `Ψ(X, W̃, Xᵢ) = C' Ψ(X, W₁, Xᵢ)`.

The source proves (4.2)(1) by specializing the variables to complex numbers of modulus one
and applying the functional equation (4.2)(3) (printed page 209). The Lean proof follows
that route directly. It applies the functional equation at each unitary parameter and
never forms the formal Laurent-series identity.

## Contents

Elementary lemmas:

- `exists_eval_ne_zero_of_lt_norm`: a nonzero complex polynomial has no root of absolute
  value larger than the sum of the absolute values of its roots.
- `lt_rpow_sub_one_of_ceil_lt`: for `q > 1` and `s > ⌈B⌉ + 1`, `B < q^(s-1)`.
- `norm_spectralPoint_one_sub_ofReal`: `|q^(-(1-s))| = q^(s-1)` for real `s`.
- `eval_mul_eval_eq_one_of_eq_inv`: if `R = p⁻¹` as rational functions and `R` has no pole
  at `t`, then `R(t) p(t) = 1`.
- `prod_comp_ne_zero`: `∏ P(xᵢ X) ≠ 0` when `P(0) = 1`.

Central translation:

- `inverseSphericalWhittaker_mul_scalar`: the spherical function satisfies
  `W(g ϖ^t; x) = (∏ xᵢ)^t W(g; x)`. The proof reads this off the symmetric spherical
  polynomial (`sphericalWhittakerPolynomial_mul_torus_const`), whose torus evaluation is the
  spherical function.
- `corankOneIntegrand_rankInclusion_translate` and `corankOne_rankInclusion_translate`:
  assume `W₁(diag(g, 1)) = W(diag(g a, 1))` and `X(g a⁻¹) = κ X(g)`. Then after the
  substitution `g ↦ g a` the integrand of `W₁` is `κ |det a⁻¹|^(s - 1/2)` times the
  integrand of `W`. Right invariance of the compatible quotient measure
  (`IsCompatible.right_invariant`) then transfers convergence from `W` to `W₁` and
  multiplies the integral by the same factor.
- `abv_det_scalar_zpow_inv`: for Jacquet's normalized absolute value,
  `|det (ϖ^m · 1)⁻¹| = q^((n+1)m)` in `GL_(n+1)`.

## The constant `essentialDualConstant`

`essentialDualConstant q n c m` is the complex number
`c^(n+1) q^(-N) (q^(-N/2))⁻¹`, with `N = (n+1)m` and `q^(-N/2)` the complex power. It
equals `c^(n+1) q^(-N/2)`. This is the constant `C'` of JPSS 1981 (5.3). The source leaves
`C'` implicit; its value is derived here as the ratio of the two series displayed there.

## The proportionality `dualSpherical_proportional`

The setting is that of `EssentialDualComparisonStatement`: `π` is a generic representation
of `GL_(n+2)(F)`. The essential vectors are `w` of `π` (pair L-polynomial `P`) and `w'` of
its inverse-transpose pullback (pair L-polynomial `P̃`), and `(c, m)` is the pair epsilon
factor of `π × 1`. Put `N = (n+1)m`, `X = q^(-s)` and
`C = essentialDualConstant q n c m`. The theorem shows that
for every `x` with `|xᵢ| = 1` there is an `a` such that, for real `s > a`, both of the
following integrals converge and the first is `C` times the second:

- the integral of the dual function `W̃ = dualComparisonModelMap w` against
  `W(·; x; ψ) = inverseSphericalWhittaker h' x`;
- the integral of the right translate `W₁` of `w'` by `diag(ϖ^m, ..., ϖ^m, 1)` against the
  same function.

Both integrated functions lie in the model for `ψ̄ = ψ.scale (-1)`. The normalization `h'`
belongs to `ψ̄`, and `inverseSphericalWhittaker h'` uses the inverse of its standard
character, so the test function transforms by `ψ`. This is the dual test `W(g; x⁻¹; ψ)` of
JPSS 1981 (4.2)(3), printed page 209, evaluated at the parameter `x` instead of `x⁻¹`. The
two characters cancel in the integrand, which therefore descends to the unipotent quotient.

With `∃ C` in front, this is exactly the hypothesis of
`dualComparison_of_unit_spherical_integrals`.

The Lean proof runs as follows.

1. `W̃` is the `ℓ'`-coefficient of the vector `v` whose `ℓ`-coefficient is `w`
   (`dualComparisonModelMap_apply`, `dualFunction_apply`, `hℓ'`).
2. The functional equation is applied to `v` at the unitary parameter `x⁻¹`. Its forward
   integral is the integral of `w` against `W(·; x⁻¹; ψ̄)`. The essential identity of `w` at
   `x⁻¹` gives that integral the continuation `1/∏ P(xᵢ⁻¹ X)`. Uniqueness of rational
   continuation (`HasRationalContinuation.unique`) identifies the forward continuation `R`
   with it. The dual integral is the integral of `W̃` against `W(·; x; ψ)`, the dual test
   `W(·; (x⁻¹)⁻¹; ψ)` of the functional equation at `x⁻¹`. It converges and equals its
   continuation `R̃` at `q^(-s)` for large real `s`.
3. The functional equation is evaluated at the point `1 - s`. For large real `s`, the point
   `q^(-(1-s))` has absolute value `q^(s-1)`, so it is not a pole of `R`. Since
   `R · ∏ P(xᵢ⁻¹ X) = 1`, the equation becomes
   `∏ P̃(xᵢ X) R̃(X) = c^(n+1) (∏ xᵢ)^(-m) q^(-N) X^(-N)`.
4. The essential identity of `w'` at `x` gives convergence of its integral and the value
   `1/∏ P̃(xᵢ X)`. Since `W(g a⁻¹; x) = (∏ xᵢ)^(-m) W(g; x)`, the translation lemma with
   `κ = (∏ xᵢ)^(-m)` and `|det a⁻¹|^(s - 1/2) = q^(-N/2) X^(-N)` gives convergence for `W₁`.
   It also gives the value `(∏ xᵢ)^(-m) q^(-N/2) X^(-N) / ∏ P̃(xᵢ X)`.
5. Comparing steps 3 and 4 gives the constant `C`. It does not depend on `x` or `s`.

## The dual comparison `essentialDualComparison_of_functionalEquation`

`essentialDualComparison_of_functionalEquation` takes `hFE` and `hinj` as hypotheses:

- `hFE : SphericalCorankOneFunctionalEquationStatement`;
- `hinj : MirabolicRestrictionInjectivityStatement`.

From them it proves `EssentialDualComparisonStatement`. It applies the reduction
`dualComparison_of_unit_spherical_integrals` with these inputs:

- injectivity for `π` and for its inverse-transpose pullback, which is generic by
  `isGeneric_inverseTransposePullback`;
- the nonzero dual functional (`dualFunctional_nonzero`);
- the restriction invariance from the two essential-vector hypotheses;
- `dualSpherical_proportional`.

## Provenance

These are internal lemmas. They implement the cited step of JPSS 1981 (5.3) from the
functional equation JPSS 1981 (4.2)(3), which the published statement
`SphericalCorankOneFunctionalEquationStatement` formalizes for unitary parameters. They
also use the published reduction of Worker 106. The only new definition is the explicit
constant `essentialDualConstant`. They assume no
functional equation or injectivity as an established result: both enter only as explicit
hypotheses of the final theorem.
