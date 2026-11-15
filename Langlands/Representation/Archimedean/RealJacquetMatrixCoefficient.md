# Matrix coefficients of real principal series against the dual principal series

Module: `Langlands.Representation.Archimedean.RealJacquetMatrixCoefficient` (namespace
`Langlands.Archimedean.RealJacquetCoefficient`).

## Purpose and provenance

This is a helper module for the proof of
`Langlands.Archimedean.RealJacquetNonvanishingSubquotientReductionStatement`
(module `RealJacquetNonvanishingProof`). It collects the analytic properties of the matrix
coefficients `g ↦ ∫_{O(n)} w(k g) ψ(k) dk` that Casselman's argument for `V ≠ 𝔫V` uses
(Wallach 1979, 4.13). These are the vanishing on orthogonal subspaces, the adjoint law for
right derivatives, the derivative along diagonal rays, and an exponential growth bound. The
statements are internal to this formalization. They are derived from Library results:
`principalSeriesOrthogonalityInvariance` and `MatrixCoefficientAnalytic.analyticAt_matrixCoefficient`
(`PrincipalSeriesMatrixCoefficientAnalytic`), and `RealPrincipalSeriesDuality.integral_rightDerivative_eq_zero`,
`rightDerivative_mul_fun`, `isModulusEquivariant_mul` (`RealPrincipalSeriesDualityProof`).
They also use `KIntegralInvariance.rightDerivative_mul_eq`, the Iwasawa decomposition
`exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact` and `GramFormula.principalSeriesCharacter_eq`.

## Notation

`G = GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, and `O(n)` is the subgroup `unitaryCompact ℝ n`
with the normalized Haar measure `RealPrincipalSeriesDuality.haarK n` (Borel σ-algebra, the
local instance `measurableSpaceK`). `R(X) = rightDerivative (matrixModel ℝ n) X`,
`R(s) f = Whittaker.rightTranslation ℂ G s f`, and `expDiagonal h s = diag(e^{s h_i})`.

## Declarations

### Bridge to the unitary-matrix measure (section `Bridge`)

- `toUG`: `O(n) ⊆ G` to `Matrix.unitaryGroup (Fin n) ℝ`; `toUnits_toUG`, `continuous_toUG`,
  `continuous_toUnits`.
- `μK n`: the push-forward of `haarK n` to `Matrix.unitaryGroup (Fin n) ℝ` (a finite measure).
- `integral_μK`: for continuous `F`, `∫ F dμK = ∫ F ∘ toUG d haarK` (`integral_map`).

### Matrix coefficients (section `Coefficient`)

- `mc w ψ g = ∫_{O(n)} w(k g) ψ(k) dk`.
- `mc_eq_matrixCoefficient`: for continuous `w, ψ`, `mc w ψ g` equals the Library's
  `MatrixCoefficientAnalytic.matrixCoefficient (μK n) w (ψ ∘ toUnits) g`.
- `continuous_mc_integrand`, `mc_add_left`, `mc_smul_left`, `mc_add_right`, `mc_smul_right`,
  `mc_sub_left`: the integrand is continuous on `O(n)`, and `mc` is linear in each function
  (for continuous functions, in the additive cases).
- `mc_one_rightTranslation`: `mc w (R(k) ψ) 1 = mc (R(k⁻¹) w) ψ 1` for `k ∈ O(n)`, by right
  invariance of `haarK`.
- `kFinite_le_principalSeries`: `O(n)`-finite functions of `realStandardModule n ds` are
  `O(n)`-finite functions of `principalSeries ℝ n (realPositionCharacter ds)`.
- `mc_eq_zero_of_orthogonal`: let `W` be a space of `O(n)`-finite functions of a real standard
  module, stable under `R(k)` (`k ∈ O(n)`) and all `R(X)`, and `ψ` continuous with
  `mc w ψ 1 = 0` for all `w ∈ W`. Then `mc w ψ g = 0` for all `w ∈ W` and `g ∈ G`. This is
  `principalSeriesOrthogonalityInvariance` with `μ = μK n`, transported by `integral_μK`.
- `mc_rightDerivative` (adjoint law): if the position characters of `ds` and `ds'` are pointwise
  inverse, `w ∈ realStandardModule n ds` and `ψ ∈ realStandardModule n ds'`, then
  `mc (R(Y) w) ψ g = -mc w (R(g Y g⁻¹) ψ) g`. Proof: `(R(Y) w)(k g) = (R(g Y g⁻¹) f)(k)` for
  `f = R(g) w` (`KIntegralInvariance.rightDerivative_mul_eq`). The product `f ψ` is smooth and
  modulus-equivariant, so `∫_{O(n)} R(Z)(f ψ) = 0` (`integral_rightDerivative_eq_zero`). The
  product rule `rightDerivative_mul_fun` then splits this integral into the two terms.
- `hasDerivAt_mc` (ray derivative): for an `O(n)`-finite `w` of a real standard module and
  continuous `ψ`, `t ↦ mc w ψ (g · expDiagonal h t)` has derivative
  `mc (R(diag h) w) ψ (g · expDiagonal h t₀)` at `t₀`. This is the derivative clause of
  `analyticAt_matrixCoefficient`, transported by `mc_eq_matrixCoefficient`.

### Growth along a diagonal ray (section `Growth`)

- `sq_le_trace_mul_transpose`: `M_{ll}² ≤ tr(M Mᵀ)`.
- `trace_mul_orth`, `trace_orth_mul`: `tr(M k (M k)ᵀ) = tr(M Mᵀ)` if `k kᵀ = 1`, and
  `tr(k M (k M)ᵀ) = tr(M Mᵀ)` if `kᵀ k = 1`.
- `abs_det_eq_one_of_mem`: `|det k| = 1` for `k ∈ O(n)`.
- `sq_le_trace_of_iwasawa`: for `x = diag(d) u k` (`u` upper unipotent, `k ∈ O(n)`),
  `d_l² ≤ tr(x xᵀ)`. `abs_prod_eq_abs_det_of_iwasawa`: `∏ |d_l| = |det x|`.
- `trace_unitary_mul_expDiagonal`, `abs_det_unitary_mul_expDiagonal`: for `κ ∈ O(n)` and
  `x = κ · expDiagonal h s`, `tr(x xᵀ) = ∑_j e^{2 s h_j}` and `|det x| = e^{s ∑_j h_j}`.
- `abs_log_le_of_bounds`: positive `y_l` with `y_l² ≤ ∑_j e^{2 s h_j}` and
  `∏ y_l = e^{s ∑_j h_j}` (`s ≥ 0`) satisfy `|log y_l| ≤ n (log n + 2 s ∑_j |h_j|)`. The upper
  bound comes from the first inequality. The lower bound comes from the product, bounding the
  other factors from above.
- `norm_principalSeriesCharacter_le`:
  `‖principalSeriesCharacter ℝ n (realPositionCharacter ds) d‖ ≤
  (∏_l (‖χ_l(1)‖ + ‖χ_l(-1)‖)) · exp(∑_l |Re σ_l| |log |d_l||)`, with `σ` the shifted exponents
  (`shiftedExponent n (realPositionExponent ds)`), from `principalSeriesCharacter_eq`.
- `exists_growth`: for every `ds` and `h` there is `c` such that for every
  `w ∈ realStandardModule n ds` and every continuous `ψ` there is `C` with
  `‖mc w ψ (expDiagonal h s)‖ ≤ C e^{c s}` for all `s ≥ 0`. Here
  `c = (∑_l |Re σ_l|) · 2n ∑_j |h_j|` depends only on `ds` and `h`. Proof: write
  `κ · expDiagonal h s = diag(d) u k'` (Iwasawa). The principal series law gives
  `w(κ a_s) = χδ(d) w(k')`. Bound `|w(k')|` and `|ψ|` by their maxima on the compact `O(n)`,
  bound `|χδ(d)|` by the previous items, and integrate (`norm_integral_le_of_norm_le_const`;
  `haarK n` is a probability measure).
