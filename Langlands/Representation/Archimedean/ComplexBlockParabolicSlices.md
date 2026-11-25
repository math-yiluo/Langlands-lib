# Slices and norm integrals for the block integration formula

Lean module: `Langlands.Representation.Archimedean.ComplexBlockParabolicSlices`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the second tools module for the proof of the
Library statement `ComplexBlockParabolicIntegrationStatement`; the proof itself is in
`ComplexBlockParabolicIntegrationProof`.

The module concerns a function `F` in the principal series of the modulus character, either on
`GL_{m+1}(ℂ)` or on `GL_{a+k+1}(ℂ)`. It provides the following.

* Norm integrals of `F` along opposite unipotent radicals. These are norm-covariant (in the sense
  of `ComplexBlockModulusBound`) and bounded on the unitary group. They give the joint
  integrability needed for the Fubini steps of the proof.
* Integrability of `F` along these radicals at every group element.
* The smooth slices `h ↦ F(diag(1, h) y) |det h|^{2a}`. They lie in the principal series of the
  modulus character of `GL_{k+1}(ℂ)`, so the published formula for `P_{k,1}` applies to them.

Notation is as in `ComplexBlockModulusBound`. `normSqC z = |z|²` and `modulusValue` come from
`ComplexMaximalParabolicIntegration`. Unprefixed names are in the namespace
`Langlands.Archimedean.ComplexBlockParabolicProof`.

## The statement

`ComplexBlockSliceStatement`: let `a, k ∈ ℕ`, let `F` lie in
`principalSeries ℂ (a + (k+1)) (modulusCharacter (a + (k+1)))` and let `y ∈ GL_{a+k+1}(ℂ)`. Then
the function `h ↦ F(diag(1, h) y) · (|det h|²)^a` on `GL_{k+1}(ℂ)` lies in
`principalSeries ℂ (k+1) (modulusCharacter (k+1))`.

It is proved as `Langlands.Archimedean.complexBlockSlice`, from `sliceT_mem`.

Provenance. Derived, internal infrastructure; no literature statement is claimed. The exponent
`2a` is the absolute value of the determinant of the action of `diag(1, h)` on the opposite
unipotent radical `M_{(k+1)×a}(ℂ)` of `P_{a,k+1}`. It turns the restriction of the modulus
character of `GL_{a+k+1}` into the modulus character of `GL_{k+1}`.

## Contents

### Exponent arithmetic (section `Exponents`)

* `rpow_modExp_succ`: `x^{σ_{m+1}(l)} (x²)⁻¹ = x^{σ_m(l)}`.
* `rpow_modExp_block`: `x^{σ_{a+k+1}(a+j)} (x²)^a = x^{σ_{k+1}(j)}`.

### The chart norm (section `ChartNorm`)

Here `F` is a function on `GL_{m+1}(ℂ)`.

* `iotaGL_borel`: `ι(diag(z) u) = diag(z, 1) ι(u)` with `ι(u)` upper unipotent.
* `det_borel`, `det_borel_ne_zero`: `det(diag(z) u) = ∏ z_i`.
* `norm_chart_iota_borel`: for norm-covariant `F`, with `b = diag(z) u`,
  `‖F(J(v,1) ι(b g))‖ = ∏_{l<m} |z_l|^{σ_{m+1}(l)} ‖F(J(v b, 1) ι(g))‖`. This uses
  `J(v,1) ι(b) = ι(b) J(v b, 1)` (`ComplexPartialJacquet.chartGL_mul_iotaGL`).
* `chartNorm F g = ∫_{ℂ^m} ‖F(J(v,1) ι(g))‖ dv`, with `chartNorm_nonneg` and `norm_chartNorm`.
* `normCov_chartNorm`: `g ↦ chartNorm F g` is norm-covariant on `GL_m(ℂ)`. Proof: the substitution
  `v ↦ v b` (`integral_vecMul_smul`, Jacobian `|det b|^{−2}`) and `prod_norm_inv_sq`.
* `chartNorm_le`: on `U(m)`, `chartNorm F κ ≤ C ∫ ∏_l (1 + |x_l|²)^{−2} dx`, by
  `norm_le_chartBound`.
* `integrable_chart_iota`: `v ↦ F(J(v,1) ι(g))` is integrable for every `g ∈ GL_m(ℂ)`. Proof:
  write `g = diag(z) u κ` (`exists_diagonalUnits_mul_upperUnipotent_mul_unitary`) and dominate by
  the chart bound composed with `v ↦ v b` (`integrable_comp_vecMul`).

### The block norm (section `BlockNorm`)

Here `F` is a function on `GL_{a+k+1}(ℂ)` and `κ₁ ∈ GL_a(ℂ)`.

* `blockDiagGL_borel`: `diag(1, diag(z) u) = diag(1_a, z) diag(1, u)` with `diag(1, u)` upper
  unipotent. This uses `ComplexBlockDual.blockDiagGL_diagonalUnits_right` and
  `blockDiagGL_mem_upperUnipotent_right`.
* `blockLowerGL_mul_blockDiagGL_mul`: `n̄(X) diag(κ₁, b h) = diag(1, b) n̄(b⁻¹ X) diag(κ₁, h)`.
* `norm_block_borel`: for norm-covariant `F`,
  `‖F(n̄(X) diag(κ₁, b h))‖ = ∏_j |z_j|^{σ_{a+k+1}(a+j)} ‖F(n̄(b⁻¹ X) diag(κ₁, h))‖`.
* `blockNorm F κ₁ h = ∫_{M_{(k+1)×a}} ‖F(n̄(X) diag(κ₁, h))‖ dX`, with `blockNorm_nonneg` and
  `norm_blockNorm`.
* `normCov_blockNorm`: `h ↦ blockNorm F κ₁ h` is norm-covariant on `GL_{k+1}(ℂ)`. Proof: the
  substitution `X ↦ b⁻¹ X` (`integral_leftMul_eq_real`, Jacobian `|det b|^{2a}`) and
  `prod_norm_block`.
* `blockNorm_le`: for `κ₁ ∈ U(a)` and `κ ∈ U(k+1)`, `blockNorm F κ₁ κ ≤ C ∫ blockBound a (k+1)`,
  by `norm_le_blockBound`.
* `integrable_block_diag`: `X ↦ F(n̄(X) diag(κ₁, h))` is integrable for every `h ∈ GL_{k+1}(ℂ)`.
  Proof: write `h = b κ` and dominate by the block bound composed with `X ↦ b⁻¹ X`
  (`integrable_comp_leftMul`).

### The slices along `GL_{k+1}(ℂ)` (section `Slice`)

* `sliceT F y h = F(diag(1, h) y) · normSqC(det h)^a`.
* `contMDiff_normSqC_det_pow`: `h ↦ normSqC(det h)^p` is smooth on `GL_N(ℂ)`.
* `modulusValue_addCases`: `δ_{a+k+1}(1_a, z) · normSqC(∏ z_j)^a = δ_{k+1}(z)`. This is an
  identity of complex powers of `|z_j|²`, using `Complex.cpow_add`.
* `sliceT_mem`: `sliceT F y` lies in the principal series of the modulus character of
  `GL_{k+1}(ℂ)`.
  * Smoothness: `ComplexBlockDual.contMDiff_comp_affine` (the embedding `h ↦ diag(1, h)` is
    affine) applied to the right translate of `F` (`rightTranslation_mem_principalSeries`),
    multiplied by the smooth factor (`contMDiff_mul_fun`).
  * Covariance: `diag(1, diag(z) u h) y = diag(1_a, z) diag(1, u) (diag(1, h) y)`, then
    `covariant`, then `modulusValue_addCases`.
* `sliceT_apply_unitary`: if `|det h| = 1`, then `sliceT F y h = F(diag(1, h) y)`.
