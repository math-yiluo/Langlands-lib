# Nonvanishing of the block Jacquet functional

Lean module: `Langlands.Representation.Archimedean.ComplexBlockNonvanishing`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It shows that the block Jacquet functional
`ComplexBlockFunctional.jac` of `ComplexBlockFunctional` is nonzero on the `U(n)`-finite principal
series. It generalizes the published `ComplexJacquetNonvanishing` (one row at a time, strictly
decreasing exponents) to blocks with tied exponents.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N` with Haar
probability measure `unitaryHaar N`. `n̄(X)` (`blockLowerGL`) and `diag(g₁, g₂)` (`blockDiagGL`)
come from `ComplexBlockParabolicIntegrationStatement`. `blockStep`, `blockPair`, `blockShiftChar`
and `IsBlockDominant` come from `ComplexBlockJacquet`. `dim`, `BlockOrdered`, `blockVector` and
`jac` come from `ComplexBlockFunctional`. `phaseMonomial`, `IsTranslateFinite` and
`bernoulli_pow` come from `ComplexJacquetNonvanishing`, and `extension` from
`ComplexPrincipalSeriesExtension`. `ComplexBlockChart.padFrom s M` is `M` on the indices `≥ s`
and the identity elsewhere; `ComplexBlockChart.gramRe y s` is the Gram determinant of the rows
`≥ s` of `y`. Unprefixed names below are in the namespace
`Langlands.Archimedean.ComplexBlockNonvanishing`.

## The statement

`ComplexBlockNonvanishingStatement` assumes `ComplexBlockChartIntegrableStatement`, which is only
stated, not yet proved, in the Library. Under that assumption it says the following.

Let `ks` be a block decomposition of `n = dim ks` and `χ` characters with
`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1` and `χ_l(u) = u^{p_l}` for `|u| = 1`, such that
`BlockOrdered ks e`. Then some `U(n)`-finite function `f` of `principalSeries ℂ n χ` satisfies
`jac ks e p f ≠ 0`.

It is proved as `Langlands.Archimedean.complexBlockNonvanishing`, from
`exists_jac_testVector_ne_zero`, with `f` a test vector (`testVector_mem`).

Provenance. Derived, internal infrastructure: nonvanishing of the Jacquet-integral functional by
an approximate identity on the opposite unipotent radical. No literature statement is claimed.

## Proof

### The approximate identity on `M_{(k+1)×a}(ℂ)` (section `Gaussian`)

For `Y : Fin (k+1) → Fin a → ℂ`:

* Definitions. `sqF Y = ∑ |Y_{ij}|²` and `detF Y = Re det(1 + Y Yᴴ)`. `eig Y` are the eigenvalues
  of the positive semidefinite `Y Yᴴ`, with `sum_eig : ∑ eig = sqF`.
* `detF_smul`: `detF(tY) = ∏ (1 + t² λ_i)`, by `ComplexBlockLimit.re_det_one_add_smul`. Also
  `detF_eq`, `one_le_detF`, `continuous_detF`.
* Monotonicity and bounds:
  * `detF_pow_mono`: `detF(Y/√N)^N` increases with `N`, via `bernoulli_pow` for each eigenvalue.
  * `one_add_sqF_le`: `(1 + sqF/M)^M ≤ detF(Y/√M)^M`, using `one_add_sum_le_prod`.
  * `detF_pow_le_exp`: `detF(Y/√M)^M ≤ exp(sqF Y)`.
* The dominating function. With `M₀ = (k+1)a + 1`, `bnd Y = (2M₀)^{M₀}(1 + ‖Y‖)^{-2M₀}` is
  integrable (`integrable_bnd`). This uses Mathlib's `integrable_one_add_norm`, since the real
  dimension is `2(k+1)a` (`finrank_rows`).
  * `inv_detF_le_bnd`: `(detF(Y/√N)^N)⁻¹ ≤ bnd Y` for `N ≥ M₀`, using `‖Y‖ ≤ √(sqF Y)`
    (`norm_le_sqrt_sqF`).
  * `exp_neg_le_bnd`, `integrable_gaussianF`.
* `tendsto_detF_pow`: `detF(Y/√N)^N → exp(sqF Y)`.
* `cG a k = ∫ exp(−sqF Y) dY`, and `cG_pos`: `cG > 0`.
* `tendsto_concentrate`: let `H` be continuous and bounded by `C`, and `N' = N + M₀`. Then
  `N'^{(k+1)a} ∫ detF(X)^{-N'} H(X) dX → cG · H(0)`. Proof:
  1. Substitute `X = Y/√N'` (`Measure.integral_comp_smul`, `sqrt_pow_rows`).
  2. Apply dominated convergence with bound `C · bnd`.

  `norm_concentrate_le` gives the uniform bound `∫ C · bnd`.

### Continuity of `jac` (section `Continuity`)

* `tendsto_of_mem_principalSeries`: for principal-series functions, pointwise convergence on
  `U(n)` gives pointwise convergence everywhere (Iwasawa decomposition).
* `tendsto_jac` (by induction on `ks`): suppose the functions `f_N` and the limit `f₀` are
  `U(n)`-finite in the principal series, and `f_N → f₀` pointwise on `U(n)` with a uniform bound.
  Then `jac ks e p f_N → jac ks e p f₀`. In the induction step, `blockPair` converges pointwise on
  `U(a)` with a uniform bound, by dominated convergence twice: in `X` with the bound
  `C · blockChartBound` (`norm_le_block`, `ComplexBlockChartIntegrableStatement`), then in `κ₂`.

### Lower-right minors (section `Minors`)

* `padFrom_mul`: for upper triangular `b`, `padFrom s (b y) = padFrom s b · padFrom s y`.
* `isUpperTriangular_padFrom` and `det_padFrom_upper`: for upper triangular `b`,
  `det(padFrom s b) = ∏_{i ≥ s} b_ii`. The helper lemmas `padFrom_apply_*` give the entries.
* `minorSq s M = |det(padFrom s M)|²`. `minorSq_mul_upper` and `minorSq_phaseMatrix`: `minorSq` is
  invariant under left multiplication by a diagonal phase matrix.

### Test vectors (section `TestVector`)

* `bumpFactor L M = ∏_{(s, N) ∈ L} minorSq s M ^ N` (`bumpFactor_cons`).
* `testFun n p av L κ = phaseMonomial n p av κ · bumpFactor L κ` on `U(n)`, and
  `testVector n e p av L = extension (shiftedExponent n e) (testFun n p av L)`.
* Translate-finiteness and continuity:
  * `isTranslateFinite_sum`, `isTranslateFinite_det` (determinants of matrices with
    translate-finite entries, via `Matrix.det_apply'`), `isTranslateFinite_padFrom_entry`;
  * `isTranslateFinite_minorSq` (`minorSq = det · conj det`), `isTranslateFinite_bumpFactor`,
    `isTranslateFinite_testFun`;
  * `continuous_minorSq`, `continuous_bumpFactor`, `continuous_testFun`;
  * `bumpFactor_phaseMatrix`.
* `testVector_mem`: test vectors are `U(n)`-finite functions of `principalSeries ℂ n χ`, by
  `extension_mem_kFiniteFunctions`. `testVector_of_mem` gives their values on `U(n)`.

### The outer bump (sections `Bump`, `Chart`)

* `bumpQ s y = minorSq s y / gramRe y s`. `bumpQ_iwasawa`: `bumpQ s (diag(z) u κ) = minorSq s κ`.
  Both the minor and the Gram determinant change by `|∏_{i ≥ s} z_i|²`, by `minorSq_mul_upper` and
  `ComplexBlockChart.prod_tail_sq_eq_gram`.
* `testVector_bump`: raising the exponent at `s` by `N` multiplies the test vector by `bumpQ s ^ N`
  on all of `GL_n(ℂ)`, since both sides are principal-series functions.
* `bumpQ_chart`: `bumpQ a (n̄(X) diag(κ₁, κ₂)) = detF(X)⁻¹`. Ingredients:
  * `padFrom_blockLower_mul_blockDiag`: `padFrom a (n̄(X) diag(A, D)) = diag(1, D)`;
  * `normSq_det_of_mem`: `|det κ₂| = 1`;
  * `gramRe_mul_unitary`: right unitary invariance of `gramRe`;
  * `gram_blockLower_rows`: the Gram determinant of the last `k+1` rows of `n̄(X)` is
    `det(1 + X Xᴴ)`.

### Restriction to the Levi factor (section `Restrict`)

* `pm n p av M` is the phase monomial as a function of a matrix (`phaseMonomial_eq_pm`).
* `pm_blockDiag`, `padFrom_blockDiag`, `minorSq_blockDiag` (for `s ≤ a` and unitary `D`),
  `bumpFactor_blockDiag`, and `minorSq_self`.
* `testVector_blockDiag`: if all bump positions are `≤ a` and `κ₁, κ₂` are unitary, then
  `testVector (a+k+1) e p av L (diag(κ₁, κ₂)) = testVector a e' p av L (κ₁) · pm_block(κ₂)`.

### The induction (section `Main`)

* `blockChartBound_le_one`: `blockChartBound ε ≤ 1` for `ε ≤ 0`. Hence `norm_chart_le`: for the
  principal series of `χ` with `IsBlockDominant`, `‖h(n̄(X) κ)‖ ≤ C`.
* `blockStep_smul`, `testVector_bump_block` (the bump identity on `GL_{a+(k+1)}`), `pow_factor`.
* `exists_integral_blockVector_pm`: `∫_{U(k+1)} blockVector a k e p · pm_block` is a positive
  real number. The integrand is `∏_j |κ_jj|^{2(|p_{a+j}| + av_{a+j})}`, which is continuous,
  nonnegative and equal to `1` at `1`. The Haar measure is positive on open sets.
* `exists_jac_testVector_ne_zero` (by induction on `ks`). It produces `av` and a list `L` of bump
  positions `≤ dim ks` such that the test vector has nonzero `jac`.
  * `ks = []`: `jac` evaluates the test vector at `1`, giving `1`.
  * `ks = k :: ks'`, `a = dim ks'`: the induction hypothesis on `GL_a(ℂ)` (exponents
    `e − (k+1)/2`) gives `av`, `L`. Set `TV_N = testVector (a+k+1) e p av ((a, N + M₀) :: L)`.
    1. By `testVector_bump_block` and `bumpQ_chart`,
       `blockStep TV_N (diag(κ₁, κ₂)) = ∫ detF(X)^{-(N+M₀)} TV_0(n̄(X) diag(κ₁, κ₂)) dX`.
    2. `tendsto_concentrate` gives
       `(N+M₀)^{(k+1)a} blockStep TV_N → cG · TV_a(κ₁) pm_block(κ₂)`, using `testVector_blockDiag`
       at `X = 0`.
    3. Dominated convergence in `κ₂` gives
       `blockPair φ ((N+M₀)^{(k+1)a} TV_N) → cG · r · TV_a` on `U(a)`, with the uniform bound
       from `norm_concentrate_le`. Here `φ = blockVector a k e p` and `r > 0` comes from
       `exists_integral_blockVector_pm`.
    4. `tendsto_jac` on `GL_a(ℂ)` gives convergence of `jac` along this sequence, and the limit
       `cG · r · jac(TV_a)` is nonzero. So for some `N`, `jac (k :: ks') e p TV_N ≠ 0`
       (`jac_cons`, `jac_smul`).
