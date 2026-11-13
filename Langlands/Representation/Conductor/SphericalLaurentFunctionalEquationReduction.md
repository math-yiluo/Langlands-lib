# Reduction of the all-parameter spherical functional equation

This internal unit is a conditional step towards the published
`SphericalLaurentFunctionalEquationStatement`. It proves that statement from two
other published statements, which it takes as hypotheses:

- `SphericalCorankOneFunctionalEquationStatement` (the functional equation for
  unitary Satake parameters, `‖x_i‖ = 1`);
- `SphericalLFactorGenerationStatement` (the standard L-polynomial, convergence and
  the Laurent numerator for every Satake parameter).

It proves no instance of either hypothesis, so it does not by itself prove the
target. Once both hypotheses are proved, the target follows by applying the final
theorem to the two proofs.

## Notation

`F` is a nonarchimedean local field, `h : IsJacquetNormalization q ψ abv ϖ μ` and
`h' := h.scaleNegOne`, Jacquet's normalizations for `ψ` and `ψ̄ = ψ.scale (-1)`.
`π` is a generic representation of `GL_(n+2)(F)` with nonzero `ψ`-Whittaker
functional `ℓ`, `π̃ := inverseTransposePullback π` (`g ↦ π(ᵗg⁻¹)`) and
`ℓ̃ := scaledDualFunctional ψ π ℓ` (from `EssentialDualSetup`). For
`x : Fin (n + 1) → ℂˣ`:

- `W(x; ψ̄)` is `inverseSphericalWhittaker h.conductor.1 h.uniformizer q x` and
  `W(x⁻¹; ψ)` is `inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹`;
- `X = q^(-s)` is `spectralPoint q s`;
- `essentialFactor P x` is the rational function `∏ i, P(x_i X)⁻¹`.

## Rational continuations from Laurent numerators

`exists_halfPlane_eval_spectralPoint_ne_zero hq D hD`: if `1 < q` and the complex
polynomial `D` satisfies `D(0) ≠ 0`, there is `b : ℝ` with `D(q^(-s)) ≠ 0` whenever
`Re s > b`.

Proof: `D` is continuous, so it has no zero in a ball of radius `δ > 0` around `0`.
Take `b = -log_q δ`. Then `|q^(-s)| = q^(-Re s) < q^(log_q δ) = δ` for `Re s > b`.

`hasRationalContinuation_laurent_mul_essentialFactor hq hP x hf`: let `1 < q`,
let `P` be a complex polynomial with `P(0) = 1`, and let `x : Fin m → ℂˣ`. Suppose
that for `Re s > a`

`f(s) ∏ i, P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))`

with `N : ℤ` and `Q` a polynomial. Then `f` has the rational continuation
(`HasRationalContinuation q`) `laurentToRatFunc (T^N Q) · essentialFactor P x`,
that is `X^N Q(X) ∏ i, P(x_i X)⁻¹`.

Proof: `D := ∏ i, P(x_i X)` has `D(0) = 1`, so `D(q^(-s)) ≠ 0` on a right half-plane
by the previous lemma. On the half-plane `Re s > max a b`, both factors are regular
at `q^(-s)`: `laurentToRatFunc_regular` for the Laurent polynomial
`T^N Q`, and `RegularAt.inv` for `essentialFactor P x = D⁻¹` (`essentialFactor_eq`).
The value is `q^(-Ns) Q(q^(-s)) / D(q^(-s))` (`eval_laurentToRatFunc`,
`laurentEval_T`, `laurentEval_toLaurent`, `eval_mul`, `eval_inv`), which equals
`f(s)` by the hypothesis.

## The final theorem

`sphericalLaurentFunctionalEquation_of_corankOne_of_generation hFE hgen` proves
`SphericalLaurentFunctionalEquationStatement.{uF, uV}` from
`hFE : SphericalCorankOneFunctionalEquationStatement.{uF, uV}` and
`hgen : SphericalLFactorGenerationStatement.{uF, uV}`.

Proof, for given `F, n, q, ψ, abv, ϖ, μ, h, ν, π, ℓ, P, c, m` as in the target:

1. **L-factor facts for `π`.** `hgen` for `(ψ, h, π, ℓ)` gives a polynomial `P₀`
   with `IsCharacterLPolynomial … π P₀`, convergence of `Ψ(s, w, W(x; ψ̄))` for every
   `w` and `x`, and a Laurent numerator
   `Ψ(s, w, W(x; ψ̄)) ∏ P₀(x_i q^(-s)) = q^(-Ns) Q(q^(-s))`. By
   `IsNormalizedGenerator.unique`, `P₀` equals the target's `P`.
2. **L-factor facts for `π̃`.** `π̃` is generic for `ψ̄`
   (`isGeneric_inverseTransposePullback`) and `ℓ̃ ≠ 0`
   (`scaledDualFunctional_ne_zero`). `hgen` for `(ψ̄, h', π̃, ℓ̃)` gives `Pdual` with
   `IsCharacterLPolynomial … π̃ Pdual`, convergence and Laurent numerators for every
   vector of the model of `ℓ̃` and every parameter. This `Pdual` is the target's
   witness; its constant term is `1` because it is a normalized generator.
3. **The dual integral.** Write `v = coefficientMap π ℓ u`, and let `ṽ` be
   `coefficientMap π̃ ℓ̃ u`, a vector of the model of `ℓ̃`. By
   `firstDualFunction_coefficient` (module `RankinSelberg/DualModels`),
   `firstDualFunction ψ (n + 1) v = ṽ`. By
   `secondDualFunction_inverseSphericalWhittaker` (module `SphericalDualParameters`), the second dual of `W(x; ψ̄)` is
   `W(x⁻¹; ψ)`. So the dual integral of the target is
   `Ψ(s, ṽ, W(x⁻¹; ψ))` for `ψ̄`.
4. **Rational continuations for every `x`.** The previous lemma, applied to the
   Laurent numerators of steps 1 and 2, gives Laurent polynomials `Q x` and `Qd x`
   with rational continuations `Q x · essentialFactor P x` of
   `Ψ(s, v, W(x; ψ̄))` and `Qd x · essentialFactor Pdual x⁻¹` of
   `Ψ(s, ṽ, W(x⁻¹; ψ))` (the latter by applying step 2 at the parameter `x⁻¹`).
5. **The unitary functional equation.** For unitary `x`, `hFE` with `h'`,
   `ℓ' := ℓ̃` (its value is `dualFunctional ψ π ℓ` by `scaledDualFunctional_val`),
   `P` and `Pdual` gives rational continuations `R` and `Rdual` of the same two
   integrals and the published `NormalizedFunctionalEquation` with root of unity
   `1`, exponent `0`, constant `c^(n+1) (∏ x_i)^m` and degree `(n + 1) m`. By
   `HasRationalContinuation.unique`, `R` and `Rdual` are the continuations of
   step 4. Since `1^0 = 1 = 1^(n+1)`, the equation also holds with exponent `n + 1`,
   as the target writes it.
6. **All parameters.** `normalizedFunctionalEquation_of_unitary` (module
   `SphericalUnitaryExtension`, by Worker 5665),
   applied with `ρ := π̃`, `w := v`, `w' := ṽ`, `ζ := 1`, `c := c^(n+1)`,
   `e := n + 1`, `k := (n + 1) m`, the convergence of steps 1 and 2 (the latter at
   `x⁻¹`), the continuations of step 4 and the unitary equation of step 5, gives the
   functional equation for every `x`.
7. **Assembly.** For the given `v` and `x`, the target's clauses are: convergence
   of the forward integral (step 1), convergence of the dual integral (step 2 at
   `x⁻¹`, rewritten by step 3), `Q := Q x` with its continuation (step 4),
   `Rdual := Qd x · essentialFactor Pdual x⁻¹` with its continuation (step 4,
   rewritten by step 3), and the functional equation (step 6).

## Provenance

Internal. The two hypotheses are published Library statements. The first is
JPSS 1981, (4.2)(3), for unitary Satake parameters. The second is JPSS 1983,
Theorems (2.7) and (3.1), with Jacquet 2012, Lemma 4. This unit adds only the
bookkeeping that combines them. It identifies the two L-polynomials through
`IsNormalizedGenerator.unique` and the continuations through
`HasRationalContinuation.unique`. It identifies the dual integral through the
dual-transform lemmas of `SphericalDualParameters`, and it extends from unitary to
all parameters through `normalizedFunctionalEquation_of_unitary` of
`SphericalUnitaryExtension`. The two
rational-continuation lemmas are elementary facts about polynomials and
`q^(-s)`. No external assertion is introduced.
