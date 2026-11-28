# Subunitary exponents at unitary parameters from the regular exponent labels

Module `Langlands.Global.AdelicEisensteinUnitaryExponentReduction`, namespace
`Langlands.Global` (helper lemmas in `Langlands.Global.UnitaryExponent`).

The main theorem is

```text
eisensteinUnitaryExponent_of_exponentLabels
  (hJ : EisensteinJointRootHyperplaneStatement.{0})
  (hL : EisensteinConstantTermExponentLabelsStatement) :
  EisensteinUnitaryExponentStatement
```

The module also states this implication as the proposition
`EisensteinUnitaryExponentReductionStatement` and proves it as
`eisensteinUnitaryExponentReduction`.

It derives the subunitary difference equations of the constant terms of a continued Eisenstein
series at unitary parameters (Lapid 2011, Proposition 4, (13) and Lemma 6; Delorme 2023,
(4.2)–(4.4)) from two statements of the Library:

- `EisensteinJointRootHyperplaneStatement` (module
  `Langlands.Global.AdelicEisensteinJointRootHyperplaneStatement`; Bernstein–Lapid 2024,
  Theorem 2.3 (1), (6) and the Corollary in §8.6): near every parameter, a power of a product
  of root forms turns the continued Eisenstein series into one function of `(λ, g)` that is
  continuous, holomorphic in `λ` and left `G(F)`-invariant in `g`;
- `EisensteinConstantTermExponentLabelsStatement` (module
  `Langlands.Global.AdelicEisensteinConstantTermExponentLabelsStatement`; Lapid's Proposition 4,
  (12), (13) and Lemma 6 at regular parameters): at sufficiently regular `λ` the constant term
  along `P_J` of `E(φ, λ)` is a sum of at most `b` functions with polynomial orbits of degree at
  most `n` along `𝔄_J`, whose unnormalized exponents `L_j λ + c_j` are affine in `λ` and
  satisfy `|a^{L_j(i x) + c_j}| ≤ δ_{P_J}(a)^{1/2}` on dominant points at every unitary
  parameter `i x`.

This file does not prove either of them. The proof is the route of items 3–5 of "Why it is true"
in `AdelicEisensteinUnitaryExponentStatement.md`; items 1–2 and the algebraic content of items
3 and 5 are the content of `EisensteinConstantTermExponentLabelsStatement`.

## The proof

Fix the data of `EisensteinUnitaryExponentStatement`, the continuation `(E, D)` and the
compact set `C`. `hL` gives `b` and `n`; the theorem takes `m = b (n + 1)`, which depends on
neither `C` nor the family. Fix a standard parabolic family `𝓕`, an index `J`, a point `x ∈ C`
and a dominant positive point `s` of `A_J` with image `a ∈ 𝔄_J`. `hL` gives `R₁`, `k ≤ b`,
labels `ν_j(λ) = L_j λ + c_j` and the expansions at `R₁`-regular `λ`; the continuation is the
Eisenstein series at `R₀`-regular `λ`.

1. *Roots.* Put `ρ_j(λ) = a^{ν_j(λ)}` (`parameterPower`). The `m` roots are each `ρ_j(λ)`
   repeated `n + 1` times, followed by `m − k (n + 1)` zeros, indexed through the equivalence
   `(Fin k × Fin (n + 1)) ⊕ Fin (m − k (n + 1)) ≃ Fin m`. Then
   `∏_q (X − ρ_q(λ)) = (∏_j (X − ρ_j(λ))^{n+1}) · X^{m − k(n+1)}` (`hprod` in the proof). Each
   root is entire in `λ` in every linear coordinate system
   (`differentiable_parameterPower_affine`). At `λ = i e(x)` the roots satisfy the required
   bound by the subunitarity of the labels, and the zeros trivially.
2. *Regular parameters.* For `λ` regular for `max R₀ R₁`, `E λ` is the Eisenstein series and
   its constant term is `∑_j f_j` with `HasPolynomialOrbit J (ν_j(λ)) n (f j)`. The Library's
   `isTranslationPolynomialSolution_pow_of_polynomialOrbit` gives that `(X − ρ_j(λ))^{n+1}`
   annihilates `f_j` under the left shift by `a`, `isTranslationPolynomialSolution_sum_prod`
   gives that the product annihilates the sum, and
   `UnitaryExponent.isTranslationPolynomialSolution_mul_right` adds the factor `X^{m − k(n+1)}`.
3. *Meromorphy of constant terms*
   (`UnitaryExponent.isMeromorphicInCoordinatesOn_subgroupConstantTerm`). For every closed
   subgroup `j : H → G` with compact quotient `H(F) \ H(𝔸)` (here the unipotent radical of
   `P_J`, compact by `compactSpace_rationalQuotient_range_unipotent`) and every `g₀`, the
   function `λ ↦ ∫_{H(F) \ H(𝔸)} E(λ)(h g₀) dh` is meromorphic in coordinates with domain of
   holomorphy `D`. In coordinates `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`:
   - every `E λ` with `λ ∈ D` is left `G(F)`-invariant
     (`eisensteinContinuation_leftRationalInvariant`);
   - `(s, g) ↦ E(e s)(g)` is continuous at every point of `e⁻¹ D × G(𝔸)`: `hJ` at that point
     gives the cleared function, and `continuousAt_of_rootHyperplane_cleared` (module
     `Langlands.Global.AdelicEisensteinImaginaryJointContinuityReduction`) expresses `E` by
     Cauchy's formula on a circle transversal to the root hyperplanes;
   - hence the constant term is holomorphic on `e⁻¹ D` by
     `UnitaryExponent.differentiableOn_subgroupConstantTerm`;
   - near an arbitrary point `s₀`, `hJ` gives a cleared function `h(s, g)` on an open `W ∋ s₀`
     with `h(s, ·) = (∏_β B(e s − e s₀, β))^k E(e s)` for `e s ∈ D`. The constant term of
     `h(s, ·)` is holomorphic on `W` by the same lemma, and the integral is linear, so on a ball
     around `s₀` the constant term of `E` times the polynomial `(∏_β B(e s − e s₀, β))^k`
     equals a holomorphic function. The polynomial is not identically zero on the ball: the
     root forms are nonzero (`exists_rootFunctional_ne_zero`), so some direction `v` avoids
     all their kernels, and `s₀ + t v` with small real `t > 0` lies in the ball off all root
     hyperplanes through `s₀`. This is the local condition of `IsMeromorphicOn`.
4. *Continuation* (`UnitaryExponent.isTranslationPolynomialSolution_of_regular`). With
   `Ψ λ = 𝓕.constantTerm J (E λ)`, for every `g` the function
   `λ ↦ ∑_{i ≤ m} c_i(λ) Ψ λ (a^i g)`, with `c_i(λ)` the coefficients of `∏_q (X − ρ_q(λ))`, is
   meromorphic in coordinates with domain `D`: the coefficients are entire
   (`UnitaryExponent.differentiable_translationRootPolynomial_coeff`), and products with entire
   functions and finite sums keep the domain (`isMeromorphicInCoordinatesOn_mul_entire`,
   `isMeromorphicInCoordinatesOn_finsetSum`). It vanishes at regular parameters by step 2, so by
   meromorphic uniqueness from the convergence chamber (`ParabolicRootPresentation.eqOn_of_regularParameter`)
   it vanishes on `D`. Since `i e(x) ∈ D`, the difference equation holds at `i e(x)`.

## Helper lemmas

In namespace `Langlands.Global.UnitaryExponent`:

- `isMeromorphicInCoordinatesOn_mul_entire`, `isMeromorphicInCoordinatesOn_finsetSum`,
  `isMeromorphicInCoordinatesOn_const_zero`: closure properties of meromorphy in coordinates
  with a fixed domain of holomorphy.
- `differentiable_translationRootPolynomial_coeff`, `differentiable_finsetProd_apply`: entire
  roots give entire coefficients of `translationRootPolynomial`; finite products of entire
  functions are entire.
- `isTranslationPolynomialSolution_mul_right`: a multiple of an annihilating polynomial
  annihilates.
- `isTranslationPolynomialSolution_of_regular`: a difference equation with entire roots for a
  family meromorphic in coordinates with domain `D` extends from the regular parameters to `D`.
- `differentiableOn_subgroupConstantTerm`: the constant term along a closed subgroup with
  compact quotient of a family `f s` of left `G(F)`-invariant functions, jointly continuous on
  `W × G(𝔸)` and holomorphic in `s ∈ W`, is holomorphic on `W`. The integrand descends to the
  quotient; it is jointly continuous there because `id × (quotient map)` is an open quotient
  map (`IsOpenQuotientMap.continuousAt_comp_iff`), hence bounded on `K × H(F) \ H(𝔸)` for
  compact `K ⊆ W`, and the Library's `differentiableOn_integral_of_bounded` applies to the
  normalized quotient measure, a probability measure.
- `isMeromorphicInCoordinatesOn_subgroupConstantTerm`: step 3 above.

## Scope

The theorem is conditional on `EisensteinJointRootHyperplaneStatement` (at universe `0`) and
`EisensteinConstantTermExponentLabelsStatement`; with proofs of both it proves
`EisensteinUnitaryExponentStatement` with the same order `m = b (n + 1)` for every compact set
`C`. The analytic continuation of the difference equations is proved here in full.
