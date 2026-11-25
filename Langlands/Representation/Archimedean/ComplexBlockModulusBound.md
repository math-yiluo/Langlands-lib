# Growth bounds for modulus-covariant functions on `GL_n(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockModulusBound`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It collects tools for the proof of the Library
statement `ComplexBlockParabolicIntegrationStatement` (the proof is in
`ComplexBlockParabolicIntegrationProof`). The tools are:

* growth bounds for functions that transform in norm like the modulus character;
* the change of variables `X ↦ h X` on `M_{r×a}(ℂ)`;
* block-matrix identities;
* a measure-preserving rearrangement of coordinates;
* two Fubini helpers.

Notation:

* `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N`.
* `n̄(X) = [[1, 0], [X, 1]]` is `blockLowerGL` and `diag(g₁, g₂)` is `blockDiagGL`; both come from
  `ComplexBlockParabolicIntegrationStatement`, and `Fin (a + r)` is split as `Fin a ⊕ Fin r`.
* `ι(g) = diag(g, 1)` is `iotaGL`, and `J(v, 1)`, the identity matrix with last row `(v, 1)`, is
  `chartGL v`; both come from `ComplexMaximalParabolicIntegration`.
* Unprefixed names below are in the namespace `Langlands.Archimedean.ComplexBlockParabolicProof`.

## The statement

`ComplexBlockModulusBoundStatement`: let `a, r ∈ ℕ` and let `F : GL_{a+r}(ℂ) → ℂ` be norm-covariant
(`NormCov (a + r) F`), that is,

`‖F(diag(z) u g)‖ = ∏_l |z_l|^{2(a+r−1−2l)} ‖F(g)‖`

for all `z ∈ (ℂˣ)^{a+r}`, upper unipotent `u` and `g`. Suppose `‖F‖ ≤ C` on `U(a+r)`. Then there is
an integrable function `B` on `M_{r×a}(ℂ) = (Fin r → Fin a → ℂ)` (Lebesgue measure) such that
`‖F(n̄(X) κ)‖ ≤ C · B(X)` for all `X` and all `κ ∈ U(a+r)`.

It is proved as `Langlands.Archimedean.complexBlockModulusBound`, with `B = blockBound a r`.

Provenance. Derived, internal infrastructure; no literature statement is claimed. The
norm-covariance condition is what one gets from functions in the principal series of the modulus
character `δ_B` of the upper triangular Borel subgroup. Here `|δ_B(diag z)| = ∏_l |z_l|^{σ_N(l)}`
with `σ_N(l) = 2(N−1−2l)` (`modExp`). Integrals of `‖F‖` along unipotent radicals satisfy the same
condition (see `ComplexBlockParabolicSlices`).

## Contents

### Norm-covariant functions (section `Cov`)

* `modExp N l = 2(N − 1 − 2l)`. `modExp_sub`: `(σ_N(l+1) − σ_N(l))/2 = −2`.
* `NormCov N F` is the norm-covariance condition above.
* `norm_modulus`: the norm of the modulus character `principalSeriesCharacter ℂ N
  (modulusCharacter N)` at `z` is `∏_l |z_l|^{σ_N(l)}`. It is computed with
  `norm_principalSeriesCharacter` and `isPhasePower_modulus`.
* `normCov_of_mem`: every function in `principalSeries ℂ N (modulusCharacter N)` is norm-covariant.
* `normCov_cast` and `norm_cast_prod` restate the condition for `g ↦ (‖F g‖ : ℂ)` with a character
  `c(z)`. This is the form of the hypothesis of the Library bounds
  `ComplexBlockChart.norm_le_gram` and `ComplexParabolicChartBound.norm_le_chart`, which need no
  smoothness.

### The block bound (section `Block`)

* `blockBound a r`:
  * for `r = 0` it is the constant `1`;
  * for `r = k + 1` it is `ComplexBlockChart.blockChartBound` with all column exponents `−2`,
    that is, `∏_{l<a} colGram(X, l)^{−2} · ∏_{1 ≤ j ≤ k} rowGram(X, j)^{−1}`.
* `integrable_blockBound`:
  * `r = 0`: Lebesgue measure on `Fin 0 → Fin a → ℂ` is a Dirac measure (`Measure.pi_of_empty`);
  * `r = k + 1`: this is `complexBlockChartIntegrable` (the proof of
    `ComplexBlockChartIntegrableStatement`, module `ComplexBlockChartIntegralProof`). The tail
    condition `∑_{l ≥ j} (−2 + 1) < 0` is `tail_neg_two`.
* `blockBound_nonneg`; `blockLower_zero_rows`, `blockLowerGL_zero_rows`: `n̄(X) = 1` when `r = 0`.
* `norm_le_blockBound_succ` (`r = k + 1`):
  1. Apply `norm_le_gram` to `g ↦ ‖F(g)‖`. With `σ = σ_{a+k+1}`, every exponent
     `(σ(l+1) − σ(l))/2` equals `−2`.
  2. The Gram determinants of `n̄(X)` are `colGram(X, l)` and `rowGram(X, j+1)`
     (`gramRe_blockLower_col`, `gramRe_blockLower_row`, `gramRe_blockLower_zero`).
  3. Since `rowGram ≥ 1` (`ComplexBlockLimit.one_le_rowGram`), `rowGram^{−2} ≤ rowGram^{−1}`.
* `norm_le_blockBound`: the bound for all `r` (the case `r = 0` is the bound on `U(a)`).

### The chart bound (section `Chart`)

* `norm_le_chartBound`: for norm-covariant `F` on `GL_{m+1}(ℂ)` bounded by `C` on `U(m+1)`, and
  `κ ∈ U(m+1)`, `‖F(J(x, 1) κ)‖ ≤ C ∏_l (1 + |x_l|²)^{−2}`. This is `norm_le_chart` applied to
  `‖F‖`, followed by `prod_partialSq_rpow_le`.
* `integrable_chartBound`: `∏_l (1 + |x_l|²)^{−2}` is integrable on `ℂ^m`.

### Left multiplication on `M_{r×a}(ℂ)` (section `LeftMul`)

* `leftMulLinearEquiv h`: the map `X ↦ h X` for `det h ≠ 0`. `swapLinearEquiv` exchanges the two
  arguments of a function `Fin a → Fin r → ℂ`.
* `det_leftMulLinearEquiv`: its complex determinant is `(det h)^a`. Proof: after conjugating by
  `swapLinearEquiv`, the map acts as `h` on each of the `a` columns (`LinearMap.det_conj`,
  `LinearMap.det_pi`, `LinearMap.det_toLin'`).
* `leftMulEquiv` is the map as a measurable equivalence. `isAddHaarMeasure_volume_mat`: Lebesgue
  measure on `M_{r×a}(ℂ)` is an additive Haar measure.
* `map_leftMulEquiv`: Lebesgue measure transforms by `|det h|^{−2a}`. This uses
  `LinearMap.det_restrictScalars` with `Algebra.norm_complex_apply` and
  `Measure.map_linearMap_addHaar_eq_smul_addHaar`, as in `ComplexBlockJacquet.map_rowMulEquiv`.
* `integral_leftMul_eq` (complex-valued) and `integral_leftMul_eq_real` (real-valued):
  `∫ f(h X) dX = |det h|^{−2a} ∫ f`. `integrable_comp_leftMul`: `X ↦ f(h X)` is integrable if `f`
  is.

### Block matrices (section `Blocks`)

* `symm_castSucc_castAdd`, `symm_castSucc_natAdd`, `symm_last` locate indices of
  `Fin (a + (k+1)) = Fin (a + k + 1)` in `Fin a ⊕ Fin (k+1)`.
* `castAdd_ne_natAdd'`, `natAdd_ne_castAdd'`, `last_ne_castSucc'`: index inequalities.
* `rowsSnoc X' x`: the `(k+1) × a` matrix with rows `X'` followed by the row `x`.
* `iota_blockLower`: `ι(n̄(X')) = n̄([X'; 0])`.
* `iota_blockDiag`: `ι(diag(A, D)) = diag(A, ι(D))`.
* `Jmat_append`: in the blocks `a, k + 1`,
  `J((x, w), 1) = [[1, 0], [[0; x], J(w, 1)]]`.

All three are proved entrywise: split the indices with `Fin.lastCases` and `Fin.addCases`, then
simplify.

### Group-level identities (section `GroupLevel`)

* `rowsSnoc_add`: `[X'; 0] + [0; x] = [X'; x]`.
* `blockLower_mul_blockDiag_Jmat`: `n̄([X'; x]) diag(1, J(w, 1)) = ι(n̄(X')) J((x, w), 1)`. The proof
  rewrites with `iota_blockLower` and `Jmat_append` and multiplies in blocks.
* `iotaGL_blockDiagGL`: `ι(diag(κ₁, τ)) = diag(κ₁, ι(τ))`.
* `blockLowerGL_mul_blockDiagGL_chart` (the chart identity):
  `n̄([X'; x]) diag(κ₁, J(w, 1) ι(τ)) = ι(n̄(X')) J((x, w), 1) ι(diag(κ₁, τ))`.
* `blockDiag_mul_blockLower` and `blockDiagGL_mul_blockLowerGL`:
  `diag(1, h) n̄(X) diag(A, 1) = n̄(h X) diag(A, h)`.
* `blockDiagGL_mem_unitaryCompact'`: `diag(g₁, g₂) ∈ U(a+r)` for unitary `g₁, g₂`.
* `normSq_det_unitary`: `|det κ| = 1` for `κ ∈ U(n)`.

### Fubini helpers (section `Fubini`)

* `integrable_prod_of_bounded`: suppose `μ` is finite, `f` is a.e. strongly measurable on `μ × ν`,
  every section `y ↦ f(x, y)` is integrable, and `∫ ‖f(x, y)‖ dν(y) ≤ M` for all `x`. Then `f` is
  integrable on `μ × ν`. The proof uses `integrable_prod_iff`.
* `integral_prod_prod`: a triple integral over `μ × (ν × ρ)` as an iterated integral.

### Rearranging coordinates (section `Rearrange`)

* `rowsChart a k : M_{k×a}(ℂ) × ℂ^{a+k} ≃ ℂ^k × M_{(k+1)×a}(ℂ)`, `(X', (x, w)) ↦ (w, [X'; x])`
  (`rowsChart_apply`). It is a composition of `MeasurableEquiv.piCongrLeft` along
  `finSumFinEquiv`, `MeasurableEquiv.sumPiEquivProdPi`, `MeasurableEquiv.piFinSuccAbove` at the
  last index, and reassociations of products.
* `measurePreserving_rowsChart`: it preserves Lebesgue measure, as a composition of
  measure-preserving maps.
* `integral_rowsChart` and `integrable_rowsChart` transfer integrals and integrability.
