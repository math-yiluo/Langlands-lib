# Analyticity of `U(n)`-finite matrix coefficients and orthogonality invariance for `GL_n(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexMatrixCoefficientAnalytic`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the Library module
`PrincipalSeriesMatrixCoefficientAnalytic` (Worker 5220, for `GL_n(ℝ)`), follows its proof step by
step and reuses its generic lemmas.

The module proves the analytic step of the Langlands lemma for principal series of `GL_n(ℂ)`. Let
`W` be a space of `U(n)`-finite functions of a principal series, stable under `U(n)` and under the
Lie algebra. A continuous function on `U(n)` orthogonal to `W` in a `U(n)`-integral pairing stays
orthogonal to every `GL_n(ℂ)`-translate of `W`. The statement is
`Langlands.Archimedean.ComplexPrincipalSeriesOrthogonalityInvarianceStatement`, proved as
`Langlands.Archimedean.complexPrincipalSeriesOrthogonalityInvariance`. For any characters of the
shape `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)` the result is
`ComplexMatrixCoefficientAnalytic.matrixCoefficient_eq_zero`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `Matrix.unitaryGroup (Fin n) ℂ`
(as a group) or `unitaryCompact ℂ n` (its image in `GL_n(ℂ)` under `Unitary.toUnits`).
`principalSeries ℂ n χ`, `complexStandardModule`, `kFiniteFunctions`,
`rightDerivative (matrixModel ℂ n) X` (written `R(X)`, the derivative of `s ↦ f(g exp(sX))` at `0`
for a complex matrix `X` viewed as a real direction) and `Whittaker.rightTranslation`
(`f ↦ (x ↦ f(x k))`) are the Library's. Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexMatrixCoefficientAnalytic`. The polarized Gram expressions
`gram`, `gramColumn`, `hatCoord`, `gramExpression`, `phaseUnit`, `complexPositionExponent` come
from `ComplexGramFormula`; the generic lemmas `differentiableAt_det`,
`differentiableAt_finset_prod`, `differentiableAt_mvPolynomial_eval`, `mem_slitPlane_of_re_pos`,
`hasDerivAt_integral_of_holomorphic`, `analyticAt_integral_of_holomorphic`,
`analyticAt_comp_ofReal` and `eq_zero_of_iteratedDeriv_eq_zero` come from the Library namespace
`Langlands.Archimedean.MatrixCoefficientAnalytic`.

## The statement

`ComplexPrincipalSeriesOrthogonalityInvarianceStatement`: for every `n`, every list `ds` of
complex characters and every submodule `W` of the functions on `GL_n(ℂ)` such that

* `W ≤ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`;
* `W` is stable under right translation by every `k ∈ unitaryCompact ℂ n`;
* `W` is stable under `R(X)` for every complex matrix `X`;

and for every finite measure `μ` on `U(n)` and every continuous `φ : U(n) → ℂ`: if
`∫ w(κ) φ(κ) dμ(κ) = 0` for every `w ∈ W`, then `∫ w(κ g) φ(κ) dμ(κ) = 0` for every `w ∈ W` and
every `g ∈ GL_n(ℂ)`. Here `w(κ)` and `w(κ g)` stand for `w (Unitary.toUnits κ)` and
`w (Unitary.toUnits κ * g)`.

The measure is arbitrary; the proof does not use invariance of `μ`. In the intended application
`μ` is the Haar probability measure on `U(n)` and `φ` the restriction to `U(n)` of a vector of a
dual principal series; then the statement says that the annihilator of a `(𝔤, K)`-submodule in
the `U(n)`-integral pairing is invariant under `GL_n(ℂ)`.

Provenance. Derived, internal infrastructure. It is a special case of the classical fact that the
closure of a `(𝔤, K)`-submodule of an admissible representation is `G`-invariant, because
`K`-finite vectors are analytic (Harish-Chandra). No source is cited for this exact form. The
proof is self-contained: instead of Harish-Chandra's analytic-vector theorem it uses the explicit
polarized Gram formula of `ComplexGramFormula`.

## Definitions

* `expDiag h t = diag(e^(t h_0), …, e^(t h_(n-1)))` in `GL_n(ℂ)`, for real `h : Fin n → ℝ` and
  real `t`; a one-parameter subgroup (`expDiag_add`, `expDiag_zero`).
* `zCurve g h z κ = κ g · diag(e^(z h_j))` and `yCurve g h z κ = conj(κ g) · diag(e^(z h_j))`,
  complex matrices for `z ∈ ℂ`, `κ ∈ U(n)`. At real `z = t` they are `κ g expDiag h t` and its
  entrywise conjugate (`zCurve_ofReal`, `yCurve_ofReal`), because the diagonal factor is real.
* `goodSet g h`: the pairs `(z, κ)` at which `gram l (zCurve g h z κ) (yCurve g h z κ)` has
  positive real part for `l = 0, …, n`. It is open (`isOpen_goodSet`) and contains all real
  points (`gram_curve_ofReal_re_pos`, from `gram_conj_re_pos`: for invertible `x`,
  `gram l x x̄ = |T_l|² > 0` by the Iwasawa decomposition and `ComplexGramFormula.gram_mul_conj`).
* `gramIntegrand s P g h φ z κ = gramExpression s P (zCurve g h z κ) (yCurve g h z κ) · φ(κ)`.
* `matrixCoefficient μ f φ g = ∫ f(κ g) φ(κ) dμ(κ)`.

## Proof

1. **Holomorphy of polarized Gram expressions** (`differentiableAt_paddedGram`,
   `differentiableAt_gram`, `differentiableAt_gramColumn`, `differentiableAt_hatCoord`,
   `differentiableAt_gramExpression`). Along a pair of curves `Z(w), Y(w)` with complex
   differentiable entries, all polarized Gram determinants and column determinants are
   polynomial in the entries, and `w ↦ gramExpression s P (Z w) (Y w)` is complex differentiable
   where every `gram l (Z w) (Y w)` has positive real part: there the bases of the powers lie in
   the slit plane. The coordinates `hatCoord i j (Y w) (Z w)` use `gram l (Y w) (Z w)`, which
   equals `gram l (Z w) (Y w)` (`gram_swap`). The continuous analogues
   (`continuousAt_gramExpression` and the lemmas before it) hold for continuous families.
2. **Holomorphic parameter integrals.** The Library's `hasDerivAt_integral_of_holomorphic` and
   `analyticAt_integral_of_holomorphic` (compact parameter space, finite measure, joint
   continuity on `closedBall z₀ R × X`, holomorphy in `z`) apply to `gramIntegrand` on a closed
   ball around each real `t₀` contained in `goodSet` for all `κ`
   (`exists_closedBall_subset_goodSet`, a tube-lemma argument on the compact `U(n)`).
3. **Analyticity and derivative** (`analyticAt_matrixCoefficient`). Let `f` be `U(n)`-finite in
   the principal series of `χ`, with `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)`. By the Gram formula
   (`ComplexGramFormula.exists_gramExpression_eq`) there is `P` with `f(x) = gramExpression s P x x̄`,
   so at real `t` the integrand `gramIntegrand s P g h φ t κ` is `f(κ g expDiag h t) φ(κ)`.
   Hence `t ↦ matrixCoefficient μ f φ (g · expDiag h t)` is the restriction to `ℝ` of a function
   holomorphic near each real point, so it is real analytic, and its derivative is the matrix
   coefficient of `R(H) f`, `H = diag(h)`: the pointwise derivative is
   `hasDerivAt_mul_expDiag_at` (from the Library's `rightDerivative_eq_fderiv` and
   `hasDerivAt_matrix_of_entries`), and it agrees with the complex derivative by uniqueness.
4. **One-parameter vanishing** (`matrixCoefficient_mul_expDiag_eq_zero`). If `W` is stable under
   `R(H)` and `matrixCoefficient μ w φ g = 0` for all `w ∈ W`, then all iterated derivatives at
   `0` of `t ↦ matrixCoefficient μ w φ (g · expDiag h t)` vanish (they are matrix coefficients of
   `R(H)^j w ∈ W`), so the real analytic function vanishes identically
   (`eq_zero_of_iteratedDeriv_eq_zero`).
5. **`KAK` decomposition** (`exists_kak`). Every `g ∈ GL_n(ℂ)` is `k₁ · expDiag h 1 · k₂` with
   `k₁, k₂ ∈ U(n)` and `h` real. Diagonalize the positive definite Hermitian matrix `g* g` by a
   unitary `U` with eigenvalues `λ_i > 0` (Mathlib's spectral theorem,
   `conjStarAlgAut_star_eigenvectorUnitary`); put `s_i = √λ_i`, `k₁ = g U diag(s)⁻¹` (unitary),
   `k₂ = U*` and `h_i = log s_i`.
6. **Orthogonality invariance** (`matrixCoefficient_eq_zero`). Write `g = k₁ expDiag h 1 k₂`.
   Right translation by `k₂` and `k₁` preserves `W`, and
   `matrixCoefficient μ w φ (g k) = matrixCoefficient μ (R(k) w) φ g`
   (`matrixCoefficient_mul_unitary`), so the hypothesis at `1` gives vanishing at `k₁`, and step 4
   carries it to `k₁ expDiag h 1`.

`complexPrincipalSeriesOrthogonalityInvariance` applies `matrixCoefficient_eq_zero` with
`e = complexPositionExponent ds` and `ComplexGramFormula.complexPositionCharacter_eq_phaseUnit_mul`.
