# Analyticity of `O(n)`-finite matrix coefficients and orthogonality invariance

Lean module: `Langlands.Representation.Archimedean.PrincipalSeriesMatrixCoefficientAnalytic`.

This module proves the analytic step of the Langlands lemma for real principal series of
`GL_n(ℝ)`. Let `W` be a space of `O(n)`-finite functions of a principal series, stable under
`O(n)` and under the Lie algebra. A continuous function on `O(n)` orthogonal to `W` in an
`O(n)`-integral pairing stays orthogonal to every `GL_n(ℝ)`-translate of `W`. The statement is
`Langlands.Archimedean.PrincipalSeriesOrthogonalityInvarianceStatement`, proved as
`Langlands.Archimedean.principalSeriesOrthogonalityInvariance`. For any characters of the shape
`χ_l(x) = χ_l(sgn x) |x|^(e_l)` the result is `MatrixCoefficientAnalytic.matrixCoefficient_eq_zero`.

The proof needs the real analyticity of `O(n)`-finite matrix coefficients. Matrix coefficients
along diagonal one-parameter subgroups are real analytic, with derivative given by the Lie
algebra action (`MatrixCoefficientAnalytic.analyticAt_matrixCoefficient`).

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ` and `O(n)` is `Matrix.unitaryGroup (Fin n) ℝ`.
`Unitary.toUnits` maps `O(n)` into `GL_n(ℝ)`, with image `unitaryCompact ℝ n`.
`principalSeries ℝ n χ`, `kFiniteFunctions`, `rightDerivative (matrixModel ℝ n) X` (written
`R(X)`) and `Whittaker.rightTranslation` (`f ↦ (x ↦ f(x k))`) are the Library's. Declarations
without a prefix are in the namespace `Langlands.Archimedean.MatrixCoefficientAnalytic`. The
Gram expressions `gramExpression`, `gram`, `gramColumn`, `complexify`, `shiftedExponent`,
`realPositionExponent` and `signUnit` come from `PrincipalSeriesGramFormula` (namespace
`Langlands.Archimedean.GramFormula`).

## The statement

`PrincipalSeriesOrthogonalityInvarianceStatement`: for every `n`, every list `ds` of real blocks
and every submodule `W` of the functions on `GL_n(ℝ)` such that

* `W ≤ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n)`;
* `W` is stable under right translation by every `k ∈ unitaryCompact ℝ n`;
* `W` is stable under `R(X)` for every real matrix `X`;

and for every finite measure `μ` on `O(n)` and every continuous `φ : O(n) → ℂ`, the following
holds. If `∫ w(κ) φ(κ) dμ(κ) = 0` for every `w ∈ W`, then `∫ w(κ g) φ(κ) dμ(κ) = 0` for every
`w ∈ W` and every `g ∈ GL_n(ℝ)`. Here `w(κ)` and `w(κ g)` stand for `w (Unitary.toUnits κ)` and
`w (Unitary.toUnits κ * g)`.

The measure is arbitrary: the proof does not use invariance of `μ`. In the intended application
`μ` is a Haar measure on `O(n)`, and `φ` is the restriction to `O(n)` of a vector of a dual
principal series. Then `∫ w(κ g) φ(κ) dμ(κ)` is the matrix coefficient `⟨R(g) w, φ⟩` of the
`O(n)`-integral pairing, so the statement says that the annihilator of `W` is invariant under
`GL_n(ℝ)`.

Provenance. Derived, internal infrastructure. It is a special case of the classical fact that the
closure of a `(𝔤, K)`-submodule of an admissible representation is `G`-invariant, because
`K`-finite vectors are analytic (Harish-Chandra). No source is cited for this exact form. The proof here is
self-contained: it does not use Harish-Chandra's analytic-vector theorem. It uses the explicit
Gram-determinant formula of `PrincipalSeriesGramFormula` instead. It is a sub-step of the planned
proof of the Langlands-quotient statement `RealStandardLanglandsQuotientStatement` (Task 6749).

## Definitions

* `expDiagonal h t = diag(e^(t h_0), …, e^(t h_(n-1)))` in `GL_n(ℝ)`, for `h : Fin n → ℝ`. It is a
  one-parameter subgroup (`expDiagonal_add`, `expDiagonal_zero`).
* `complexCurve g h z κ = complexify(κ g) · diag(e^(z h_j))`, a complex matrix for `z ∈ ℂ` and
  `κ ∈ O(n)`. At real `z = t` it is the complexification of `κ g expDiagonal h t`
  (`complexCurve_ofReal`).
* `goodSet g h`: the set of pairs `(z, κ)` at which the Gram determinants
  `gram l (complexCurve g h z κ)`, `l = 0, …, n`, all have positive real part. It is open
  (`isOpen_goodSet`) and contains all real points (`gram_complexCurve_ofReal_re_pos`, from
  `GramFormula.gram_pos`).
* `gramIntegrand s P g h φ z κ = gramExpression s P (complexCurve g h z κ) · φ(κ)`.
* `matrixCoefficient μ f φ g = ∫ f(κ g) φ(κ) dμ(κ)`.

## Proof

1. **Holomorphy of Gram expressions** (`differentiableAt_gramExpression`,
   `continuousAt_gramExpression`). Determinants, padded Gram matrices, `gramColumn` and
   `MvPolynomial.eval` are polynomial in the entries. So along a curve `Z(w)` with complex
   differentiable entries, `w ↦ gramExpression s P (Z w)` is complex differentiable where every
   `gram l (Z w)` has positive real part: there the base of each power lies in the slit plane,
   where `Complex.cpow` is holomorphic. The continuous analogue holds for continuous families.
2. **Holomorphic parameter integrals** (`hasDerivAt_integral_of_holomorphic`,
   `analyticAt_integral_of_holomorphic`). Let `X` be a compact space with a finite Borel measure,
   and let `F(z, x)` be jointly continuous on `closedBall z₀ R × X` and holomorphic in `z` on
   `ball z₀ R`. Then `z ↦ ∫ F(z, x) dx` has derivative `∫ ∂_z F(z₀, x) dx` at `z₀`. The proof
   bounds `‖F‖ ≤ C` by compactness, bounds `‖∂_z F‖ ≤ C/(R/2)` on `ball z₀ (R/2)` by the Cauchy
   estimate (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), and applies
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The measurability of `x ↦ ∂_z F(z₀, x)`
   comes from writing it as a limit of difference quotients. The integral is therefore holomorphic
   on `ball z₀ (R/2)`, hence analytic at `z₀`.
3. **Analyticity of matrix coefficients** (`analyticAt_matrixCoefficient`). Let `f` be
   `O(n)`-finite in the principal series of `χ`. By the Gram formula
   (`GramFormula.exists_gramExpression_eq`),
   `f(κ g expDiagonal h t) φ(κ) = gramIntegrand (shiftedExponent n e) P g h φ t κ` for real `t`.
   For `t₀ ∈ ℝ`, the tube lemma (`IsCompact.eventually_forall_of_forall_eventually` on the compact
   `O(n)`) gives `R > 0` such that `closedBall t₀ R × O(n) ⊆ goodSet g h`
   (`exists_closedBall_subset_goodSet`). On that tube the integrand is continuous and holomorphic
   in `z`, by step 1. By step 2, `z ↦ ∫ gramIntegrand … z κ dμ` is analytic at `t₀`. Its
   restriction to `ℝ` (`analyticAt_comp_ofReal`) is `t ↦ matrixCoefficient μ f φ (g expDiagonal h t)`.
   The derivative of this real function at `t₀` is `matrixCoefficient μ (R(H) f) φ (g expDiagonal h t₀)`,
   `H = diag(h)`. Indeed, the complex derivative of the integral restricts to the real
   derivative (`HasDerivAt.comp_ofReal`). Pointwise in `κ`, the complex derivative of the integrand
   at the real point equals the real derivative of `t ↦ f(κ g expDiagonal h t) φ(κ)`, which is
   `(R(H) f)(κ g expDiagonal h t₀) φ(κ)` (`hasDerivAt_mul_expDiagonal_at`, from
   `rightDerivative_eq_fderiv` of the Library). The two agree by uniqueness of derivatives.
4. **One-parameter vanishing** (`matrixCoefficient_mul_expDiagonal_eq_zero`). If `W` is stable
   under `R(H)` and `matrixCoefficient μ w φ g = 0` for all `w ∈ W`, then by step 3 the `j`-th
   derivative at `0` of `t ↦ matrixCoefficient μ w φ (g expDiagonal h t)` is the value at `0` for
   `R(H)^j w ∈ W`, which is `0`. A real analytic function on `ℝ` all of whose derivatives vanish
   at `0` is zero (`eq_zero_of_iteratedDeriv_eq_zero`: infinite analytic order, then the identity
   theorem on the connected `ℝ`).
5. **`KAK` decomposition** (`exists_kak`). For `g ∈ GL_n(ℝ)`, `gᵀ g` is positive definite. The
   spectral theorem (`Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`) gives an
   orthogonal `U` with `Uᵀ gᵀ g U = diag(λ)`, `λ_i > 0`. With `s_i = √λ_i`,
   `k₁ = g U diag(s)⁻¹` is orthogonal and `g = k₁ · expDiagonal (log s) 1 · Uᵀ`.
6. **Invariance** (`matrixCoefficient_eq_zero`). Right translation moves `O(n)`-factors from the
   group element to the function:
   `matrixCoefficient μ w φ (g k) = matrixCoefficient μ (R(k) w) φ g`
   (`matrixCoefficient_mul_unitary`). Write `g = k₁ exp(H) k₂` by step 5. The hypothesis at `1`
   and stability under `O(n)` give vanishing at `k₁` for all `w ∈ W`. Step 4 gives vanishing at
   `k₁ exp(tH)`, and stability under `O(n)` once more gives vanishing at `k₁ exp(H) k₂`.
7. **Real blocks.** `principalSeriesOrthogonalityInvariance` applies step 6 to the position
   characters of `ds`, with the exponents `GramFormula.realPositionExponent ds`
   (`GramFormula.realPositionCharacter_eq_signUnit_mul`).
