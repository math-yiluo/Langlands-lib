# Nonvanishing of the block Jacquet functional on `GL_n(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockNonvanishing`.

This module was written for the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`); the
Library's proof of that statement goes through `realLeviLanglandsQuotient` and does not import
this module. It
shows that the block Jacquet functional `RealBlockFunctional.jac` of the module
`RealBlockFunctional` is not identically zero on the `O(n)`-finite principal series. Together
with `RealBlockFunctional.jac_eq_zero_of_proper`, this shows that the
sum of all proper `(𝔤, K)`-submodules is proper; this module does not carry out that assembly. It generalizes the published `JacquetNonvanishing` (one row at
a time, strictly decreasing exponents). The module is the real analogue of
`ComplexBlockNonvanishing` and follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`, with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `IsSignedPower χ e` (module
`PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`. `signMonomial n p a κ = ∏_l κ_ll^{p_l + 2 a_l}` and its principal-series extension
`signVector` come from `JacquetNonvanishing`; `extension`, `extension_mem_kFiniteFunctions` and
`signDiagonal` from `PrincipalSeriesExtension`; `IsTranslateFinite` from `TranslateFinite`;
`gram s y` (the determinant of the Gram matrix of the rows `≥ s` of `y`) from
`PrincipalSeriesGramFormula`. `n̄(X)`, `diag(g₁, g₂)` (`blockLowerGL`, `blockDiagGL`) come from
`RealBlockParabolicIntegrationStatement`; `padFrom`, `blockChartBound`, `colGram`, `rowGram` from
`RealBlockChartIntegralStatement` and `RealBlockChartBound`; `blockStep`, `blockPair` from
`RealBlockJacquet`; `dim`, `BlockOrdered`, `blockVector` and `jac` from `RealBlockFunctional`.
Unprefixed names below are in the namespace `Langlands.Archimedean.RealBlockNonvanishing`.

## The statement

`RealBlockNonvanishingStatement` assumes `RealBlockChartIntegrableStatement`, which the Library
proves as `realBlockChartIntegrable` (`RealBlockChartIntegralProof`). Under that assumption it says: let `ks` be a
block decomposition, `n = dim ks`, and `χ` characters with `χ_l(x) = χ_l(sgn x) |x|^{e_l}`,
`χ_l(1) = 1` and `χ_l(−1) = (−1)^{p_l}` (`p : ℕ → ℕ`), such that `BlockOrdered ks e`. Then some
`O(n)`-finite function `f` of `principalSeries ℝ n χ` has `jac ks e p f ≠ 0`.

It is proved as `Langlands.Archimedean.realBlockNonvanishing`, from
`exists_jac_testVector_ne_zero`. The condition `‖χ_l(−1)‖ = 1` follows from
`χ_l(−1) = (−1)^{p_l}`.

Provenance. Derived, internal infrastructure: the nonvanishing of the leading-term functional of
the Langlands lemma for a parabolic subgroup with tempered-up-to-twist blocks. No literature
statement is claimed.

## Proof

### The approximate identity on `M_{(k+1)×a}(ℝ)` (section `Gaussian`)

For `Y : Fin (k+1) → Fin a → ℝ` put `sqF Y = ∑ Y_ij²` and `detF Y = det(1 + Y Yᵀ)`.

* `eig Y` are the eigenvalues of the positive semidefinite `Y Yᵀ` (`posSemidef_gram`,
  `eig_nonneg`); `sum_eig`: they sum to `sqF Y` (trace). `detF_smul`:
  `detF(t Y) = ∏_i (1 + t² eig_i)` (`RealBlockLimit.det_one_add_smul_eq_prod`); `detF_eq`,
  `one_le_detF`, `continuous_detF`.
* `detF_pow_mono` (Bernoulli, `JacquetNonvanishing.bernoulli_pow`): `N ↦ detF(Y/√N)^N` increases.
  `one_add_sqF_le`: `(1 + sqF/M)^M ≤ detF(Y/√M)^M` (`one_add_sum_le_prod`).
* `M₀ = (k+1)a + 1`, `finrank_rows` (`(k+1)a`), the dominating function
  `bnd Y = (2M₀)^{M₀} (1 + ‖Y‖)^{−2M₀}`, integrable (`integrable_bnd`, from
  `integrable_one_add_norm`). `inv_detF_le_bnd`: `detF(Y/√N)^{−N} ≤ bnd Y` for `N ≥ M₀`
  (`norm_le_sqrt_sqF`).
* `tendsto_detF_pow`: `detF(Y/√N)^N → exp(sqF Y)`; `detF_pow_le_exp`, `exp_neg_le_bnd`,
  `integrable_gaussianF`, `cG = ∫ exp(−sqF)` with `cG_pos`.
* `tendsto_concentrate`: with `N' = N + M₀`, for continuous `H` bounded by `C`,
  `√N'^{(k+1)a} ∫ detF(X)^{−N'} H(X) dX → cG · H(0)`. The proof substitutes `X = Y/√N'`
  (`Measure.integral_comp_smul`, `sqrt_pow_rows`) and applies dominated convergence with
  `C · bnd`. `norm_concentrate_le` bounds the left side by `∫ C · bnd` for every `N`.

### Continuity of `jac` (section `Continuity`)

* `tendsto_of_mem_principalSeries`: pointwise convergence on `O(n)` of principal-series functions
  gives pointwise convergence on `GL_n(ℝ)` (Iwasawa decomposition).
* `tendsto_jac` (induction on `ks`): if `f_N → f₀` pointwise on `O(n)` with a uniform bound there,
  then `jac ks e p f_N → jac ks e p f₀`. Each step uses dominated convergence twice: in `X` with the
  integrable bound `C · blockChartBound` (`RealBlockLimit.norm_le_block`, the statement `T1`) and in
  `κ₂ ∈ O(k+1)` with a constant bound (`RealBlockJacquet.norm_blockStep_le`).

### Test vectors (sections `Minors`, `TestVector`)

* `padFrom_mul`, `isUpperTriangular_padFrom`, `det_padFrom_upper`: for upper triangular `b`,
  `padFrom s (b y) = padFrom s b · padFrom s y` and `det padFrom s b = ∏_{i ≥ s} b_ii`.
* `minorSq s M = (det M_{≥s,≥s})² = (det padFrom s M)²`; `minorSq_mul_upper`;
  `minorSq_signDiagonal`: it is invariant under the sign matrices.
* `isTranslateFinite_sum`, `isTranslateFinite_prod`, `isTranslateFinite_det`,
  `isTranslateFinite_padFrom_entry`, `isTranslateFinite_minorSq`: polynomial functions of the
  entries of `κ ∈ O(n)` have finite-dimensional spans of right translates.
* `bumpFactor L M = ∏_{(s,N) ∈ L} minorSq_s(M)^N` (`isTranslateFinite_bumpFactor`,
  `continuous_bumpFactor`, `bumpFactor_signDiagonal`).
* `testFun n p a L κ = signMonomial n p a κ · bumpFactor L κ` and
  `testVector n e p a L = extension (shiftedExponent n e) (testFun n p a L)`: by
  `extension_mem_kFiniteFunctions`, an `O(n)`-finite function of the principal series of `χ`
  (`testVector_mem`, using `signMonomial_signDiagonal`), equal to `testFun` on `O(n)`
  (`testVector_of_mem`).

### The bump (sections `Bump`, `Chart`)

* `bumpQ s y = minorSq s y / gram s y` is left invariant under the Borel subgroup:
  `bumpQ_iwasawa` gives `bumpQ s (diag(z) u κ) = minorSq s κ` (both numerator and denominator
  pick up `(∏_{i ≥ s} z_i)²`, `RealBlockChart.prod_tail_sq_eq_gram`).
* `testVector_bump`: raising the exponent of the minor at `s` by `N` multiplies the test vector by
  `bumpQ_s^N` (Iwasawa decomposition and `testVector_of_mem`).
* `gram_blockLower_rows`: `gram a (n̄(X)) = det(1 + X Xᵀ)`; `padFrom_blockLower_mul_blockDiag`:
  `padFrom a (n̄(X) diag(A, D)) = diag(1, D)`; `det_sq_of_mem`: `(det κ)² = 1` on `O(n)`.
* `bumpQ_chart`: `bumpQ_a(n̄(X) diag(κ₁, κ₂)) = detF(X)^{−1}` for orthogonal `κ₁, κ₂`
  (`ParabolicChartBound.gram_mul_orthogonal`).

### Restriction to the Levi factor (section `Restrict`)

* `pm n p a M = ∏_l M_ll^{p_l + 2 a_l}` (`signMonomial_eq_pm`), `pm_blockDiag`:
  `pm(diag(A, D)) = pm(A) · pm_block(D)` with the shifted indices.
* `padFrom_blockDiag`, `minorSq_blockDiag`, `bumpFactor_blockDiag` (for minors at `s ≤ a` and
  orthogonal `D`), `minorSq_self` (`minorSq_a = 1` on `GL_a`).
* `testVector_blockDiag`: on `diag(κ₁, κ₂)` with orthogonal `κ₁, κ₂`, the test vector of
  `GL_{a+k+1}(ℝ)` (minors at positions `≤ a`) is the test vector of `GL_a(ℝ)` (any exponents) at
  `κ₁` times `pm_block(κ₂)`.

### Nonvanishing (section `Main`)

* `blockChartBound_le_one` and `norm_chart_le`: for `BlockOrdered` exponents the chart bound is at
  most `1`, so `|h(n̄(X) κ)| ≤ sup_{O(n)} |h|`.
* `blockStep_smul`, `testVector_bump_block`.
* `exists_integral_blockVector_pm`: `∫_{O(k+1)} blockVector(κ₂) · pm_block(κ₂) dκ₂ = r > 0`. The
  integrand is `∏_j (κ₂,jj²)^{p_{a+j} + a_{a+j}}`, continuous, nonnegative and `1` at the identity
  (`integrable_of_continuous_unitary_real`).
* `exists_jac_testVector_ne_zero` (induction on `ks`). For `ks = []`, `jac` is evaluation at `1` and
  the test vector with no factors is `1` there. For `ks = k :: ks'`, `a = dim ks'`: the induction
  hypothesis on `GL_a(ℝ)` (exponents `e − (k+1)/2`, `RealBlockJacquet.isSignedPower_blockShift`)
  gives `av`, `L` with `jac ks' (e − (k+1)/2) p (testVector a … av L) ≠ 0`. Consider the test
  vectors `h_N = testVector (a+k+1) e p av ((a, N + M₀) :: L)`. Then `blockStep h_N` at
  `diag(κ₁, κ₂)` is `∫ detF(X)^{−(N+M₀)} h_0(n̄(X) diag(κ₁, κ₂)) dX` (`testVector_bump_block`,
  `bumpQ_chart`), so by `tendsto_concentrate` (with `norm_chart_le`)
  `√N'^{(k+1)a} blockStep h_N (diag(κ₁, κ₂)) → cG · testVector_a(κ₁) · pm_block(κ₂)`
  (`testVector_blockDiag`, `blockLowerGL_zero`), uniformly bounded (`norm_concentrate_le`).
  Dominated convergence over `O(k+1)` and `exists_integral_blockVector_pm` give
  `blockPair blockVector (√N'^{(k+1)a} h_N) → cG · r · testVector_a` pointwise on `O(a)`, with a
  uniform bound. By `tendsto_jac`, `jac` of these converges to `cG · r · jac(testVector_a) ≠ 0`,
  so it is nonzero for some `N`; by `jac_smul` and `jac_cons`, `jac (k :: ks') e p h_N ≠ 0`.
