# The Jacquet integral does not vanish on strictly dominant complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetNonvanishing`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the module
`JacquetNonvanishing` for `GL_n(ℝ)`, and follows its proof; the sign monomials of the
real case become phase monomials in `κ` and `κ̄`.

Let `χ` be strictly dominant phase-power characters of `GL_n(ℂ)` whose restrictions to the unit
circle are integral powers, `χ_l(u) = u^{p_l}`. The module shows that the Jacquet integral `Λ_n`
(`ComplexJacquetDual.jacquet`) is a nonzero functional on the `U(n)`-finite principal series
(`ComplexJacquetNonvanishing.exists_jacquet_ne_zero`). The main statement is
`Langlands.Archimedean.ComplexJacquetNonvanishingStatement`, proved as
`Langlands.Archimedean.complexJacquetNonvanishing`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` or
`Matrix.unitaryGroup (Fin n) ℂ`. `chartGL` (`J(x,1)`), `iotaGL` (`ι(g) = diag(g,1)`),
`Jmat`, `sqNorm_lastRow` come from `ComplexMaximalParabolicIntegration`; `sqNorm`
(`|x|² = ∑ |x_j|²`), `gaussian` (`e^{−|x|²}`), `chartWeight`, `integral_comp_complex_smul`,
`integral_gaussian_pos` from `ComplexLastRowIntegral`; `IsPhasePower`, `IsStrictlyDominant`,
`chartExponent`, `shiftChar`, `jacquetStep` (`T`), `jacquetStep_mem`,
`norm_le_of_mem_principalSeries` from `ComplexPartialJacquet`; `jacquet` from
`ComplexJacquetDual`; `jacquet_smul` from `ComplexJacquetKernel`; `phaseUnit` (`z/|z|`) from
`ComplexGramFormula`; `phaseMatrix`, `extension`, `extension_mem_kFiniteFunctions`,
`extension_unitary` from `ComplexPrincipalSeriesExtension`. Declarations without a prefix are in
the namespace `Langlands.Archimedean.ComplexJacquetNonvanishing`.

## The statement

`ComplexJacquetNonvanishingStatement`: let `χ_l : ℂˣ → ℂ`, `e : ℕ → ℂ` and `p : ℕ → ℤ` satisfy
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `χ_l(z/|z|) = (z/|z|)^{p_l}`, and
`Re e_{l+1} < Re e_l` whenever `l + 1 < n`. Then some `U(n)`-finite function `f` of
`principalSeries ℂ n χ` has `jacquet n f ≠ 0`.

In the intended application to the characters of a list of `ComplexCharacterData`, `p_l` is the
weight of the `l`-th character (this is checked where the statement is applied, not here).
`complexJacquetNonvanishing` derives `|χ_l(z/|z|)| = 1` from it (`norm_zpow`, `norm_phaseUnit`).

Provenance. Derived, internal infrastructure: nonvanishing of the Jacquet integral (the
"leading coefficient" of the Langlands lemma), proved by an approximate identity along the
maximal parabolic subgroups. No literature claim beyond this standard argument.

## Continuity of `Λ_n`

`tendsto_jacquet`: let `f_N, f₀` be in the `U(n)`-finite principal series of `χ`, with
`|f_N| ≤ C` on `U(n)` for every `N` and `f_N → f₀` pointwise on `U(n)`. Then
`Λ_n(f_N) → Λ_n(f₀)`. By recursion on `n`: at each step `T f_N → T f₀` pointwise on `U(m)` by
dominated convergence, with the dominating function `C ∏ (1 + |x_l|²)^{chartExponent e l}` of
`norm_le_of_mem_principalSeries`. Pointwise convergence at chart points `y = diag(a) u κ` follows
from `f_N(y) = χδ^{1/2}(a) f_N(κ)` (Iwasawa decomposition,
`ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`), and
`|T f_N| ≤ C ∫ (dominating function)` on `U(m)`.

## Translate-finite functions on `U(n)`

`IsTranslateFinite f`: the right translates `x ↦ f(x k)`, `k ∈ U(n)`, span a finite-dimensional
space. It holds for constants and is preserved by sums, products, powers and finite products
(`isTranslateFinite_const`, `_add`, `_mul` (through `Submodule.FG.mul`), `_pow`, `_prod`). The
entries `κ ↦ κ_ij` and their conjugates `κ ↦ conj κ_ij` are translate-finite, since
`(x k)_ij = ∑_l x_il k_lj` (`isTranslateFinite_entry`, `isTranslateFinite_conj_entry`).

## Phase monomials and phase vectors

* `phaseMonomial n p a κ = ∏_l κ_ll^{p⁺_l + a_l} · conj(κ_ll)^{p⁻_l + a_l}` on `U(n)`, for
  `a : ℕ → ℕ`, with `p⁺ = (p).toNat`, `p⁻ = (−p).toNat`. It is continuous and translate-finite
  (`finiteDimensional_phaseMonomial`). Under `phaseMatrix d = diag(d/|d|)` on the left it
  transforms by the character of `χ`: with `u = d_l/|d_l|`, `conj u = u⁻¹`
  (`conj_eq_inv_of_norm_eq_one`) and `u^{p⁺+a} (u⁻¹)^{p⁻+a} = u^{p}`
  (`pow_mul_inv_pow_eq_zpow`), and the principal-series character on phases is `∏ χ_l(u_l)`
  (`principalSeriesCharacter_phase`) (`phaseMonomial_phaseMatrix`).
* `phaseVector n e p a` is its extension (`extension (shiftedExponent n e)`). It lies in the
  `U(n)`-finite principal series of `χ` (`phaseVector_mem`, from
  `extension_mem_kFiniteFunctions`) and equals the monomial on `U(n)` (`phaseVector_unitary`,
  `phaseVector_of_mem`).
* `phaseVector_iota`: `phaseVector (m+1) e p a (ι(k)) = phaseVector m e' p a (k)` for `k ∈ U(m)` and
  any `e'`, because the last diagonal entry of `ι(k)` is `1`.
* `qFun y = |y_mm|² / ∑_j |y_mj|²` (last row) is invariant under left multiplication by
  `diag(b) u` (`qFun_mul`, from `lastRow_diagonalUnits_mul`), equals `|κ_mm|²` on `U(m+1)`
  (`qFun_of_mem`) and `(1 + |x|²)⁻¹` at `J(x,1) ι(k)` for `k ∈ U(m)` (`qFun_chart`, from
  `lastRow_chartGL_mul_iotaGL` and `sqNorm_vecMul`).
* `phaseVector_bump`: adding `N` to the last exponent (`bump a m N`) multiplies the phase vector
  by `q^N` on all of `GL_{m+1}(ℂ)`. Both sides transform by `χδ^{1/2}` on the left and agree on
  `U(m+1)`, where `κ_mm^N conj(κ_mm)^N = |κ_mm|^{2N}`.

## The approximate identity

`tendsto_concentrate`: for `H` in the principal series of `χ`, `k ∈ U(m)` and `N' = N + m + 1`,

`N'^m ∫_{ℂ^m} (1 + |x|²)^{−N'} H(J(x,1) ι(k)) dx → (∫_{ℂ^m} e^{−|y|²} dy) · H(ι(k))`.

* The substitution `x = N'^{−1/2} y` (`integral_scale`, from `integral_comp_complex_smul`: real
  dimension `2m`, so the Jacobian is `N'^m = √N'^{2m}`; `sqNorm_scale`) turns the left side into
  `∫ (1 + |y|²/N')^{−N'} H(J(N'^{−1/2}y,1) ι(k)) dy`.
* Pointwise, `(1 + s/N')^{N'} → e^s` (`Real.tendsto_one_add_div_pow_exp`) and
  `J(N'^{−1/2}y, 1) → J(0,1) = 1`.
* Domination: Bernoulli's inequality (`bernoulli_pow`, from `one_add_mul_self_le_rpow_one_add`)
  gives `(1 + s/(m+1))^{m+1} ≤ (1 + s/N')^{N'}`, and `y ↦ (1 + |y|²/(m+1))^{−(m+1)}` is integrable
  on `ℂ^m` (`integrable_inv_one_add_div_pow`, by comparison with `chartWeight`). Also `|H| ≤ C`
  at chart points (`norm_chart_le_of_mem`, all chart exponents being negative).

`norm_concentrate_le` gives the corresponding uniform bound.

## Nonvanishing

`exists_jacquet_phaseVector_ne_zero`, by recursion on `n`.

* `n = 0`. The phase vector is `1` at `1` (`phaseVector_zero_one`), and `Λ_0` is evaluation at
  `1`.
* `n = m + 1`. `shiftChar χ` has the same phases (`shiftChar_phase`), so the recursion hypothesis
  gives `a` with `Λ_m(phaseVector m (e − 1/2) p a) ≠ 0`. Put
  `F_N = N'^m · phaseVector (m+1) e p (bump a m N')`. On `U(m)`,
  `T F_N(k) = N'^m ∫ (1+|x|²)^{−N'} phaseVector (m+1) e p a (J(x,1) ι(k)) dx` (by
  `phaseVector_bump` and `qFun_chart`). By the approximate identity and `phaseVector_iota`, this
  converges boundedly to `c · phaseVector m (e − 1/2) p a (k)` with `c = ∫ e^{−|y|²} dy > 0`. By
  `tendsto_jacquet`, `Λ_{m+1}(F_N) = Λ_m(T F_N) → c Λ_m(phaseVector m (e − 1/2) p a) ≠ 0`. So
  `Λ_{m+1}(F_N) ≠ 0` for some `N`, and by `jacquet_smul` the phase vector with exponents
  `bump a m N'` has nonzero Jacquet integral.

`exists_jacquet_ne_zero` and `complexJacquetNonvanishing` restate this.
