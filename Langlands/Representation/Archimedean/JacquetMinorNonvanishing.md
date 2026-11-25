# The Jacquet integral of a principal minor vector does not vanish

Lean module: `Langlands.Representation.Archimedean.JacquetMinorNonvanishing`.

This module was written for the proof of
`RealStandardIrreducibleCriterionStatement`. It supplies the test vector for the proof of
`RealReverseIntertwinerKernelStatement`, which says that an intertwiner from a standard module to
the reversed one kills every proper `(g, K)`-submodule. Take a real principal series of
signed-power characters `χ_0, …, χ_{n−1}` with strictly decreasing real exponents. Let
`A = {l | χ_l(−1) = −1}`. The module builds the vector `φ_{A,A}` of this principal series whose
restriction to `O(n)` is the principal minor `κ ↦ det κ_{A,A}`. It proves that the full Jacquet
integral `Λ_n` of the Library module `JacquetDual` does not vanish on `φ_{A,A}`.

Notation. `GL_n = Langlands.GeneralLinear n ℝ`, and `O(n)` is `unitaryCompact ℝ n` or
`Matrix.unitaryGroup (Fin n) ℝ`. For finite sets `A, B ⊆ {0, …, n−1}`, `det X_{A,B}` is
`MatrixMinor.minor X A B`: the determinant of the submatrix with rows `A` and columns `B`, both
in increasing order, and `0` when `|A| ≠ |B|`. `χδ^{1/2}(a) = principalSeriesCharacter ℝ n χ a
= ∏_l χ_l(a_l) |a_l|^{(n−1)/2 − l}`. `IsSignedPower χ e` means
`χ_l(y) = χ_l(sgn y) |y|^{e_l}` with `χ_l(1) = 1` and `|χ_l(−1)| = 1`; `IsStrictlyDominant e m`
means `Re e_{l+1} < Re e_l` for `l < m`. "The sign condition for `A`" is the hypothesis
`χ_l(−1) = −1` for `l ∈ A` and `χ_l(−1) = 1` for `l ∉ A`, for `l < n`.

The Library objects used are these. `J(x, 1) = chartGL x ∈ GL_{m+1}` for `x ∈ ℝ^m` is the chart
of the opposite unipotent radical of `P_{m,1}`, and `ι(g) = iotaGL g = diag(g, 1)`. The partial
Jacquet integral is `T h(g) = jacquetStep h g = ∫_{ℝ^m} h(J(x, 1) ι(g)) dx`. The full Jacquet
integral is `Λ_n = JacquetDual.jacquet n`, with `Λ_0 h = h(1)` and `Λ_{m+1} h = Λ_m(T h)`. The
shifted characters are `χ''_l(y) = χ_l(y) |y|^{−1/2}` (`PartialJacquet.shiftChar`). Lebesgue
measure on `ℝ^m` is `volume` on `Fin m → ℝ`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.JacquetMinor`.

Provenance. This is derived internal infrastructure with no literature source. It follows the
template of the Library module `JacquetNonvanishing`, which proves that `Λ_n` does not vanish on
some sign vector by an approximation argument. Here the vector is the explicit principal minor
`φ_{A,A}`, and the nonvanishing comes from the exact iterated integral of `PartialSqIntegral`. The
module makes no literature claim.

## Main results

Minor functions on `O(n)`:

- `minorFun n A B κ = det κ_{A,B}`, a complex-valued function on `O(n)`; `continuous_minorFun`.
- `minorFun_mul` (Cauchy–Binet): for `|B| = |A|` and `κ, k ∈ O(n)`,
  `det (κk)_{A,B} = ∑_{|C| = |A|} det k_{C,B} · det κ_{A,C}`.
- `finiteDimensional_minorFun`: for `|B| = |A|`, the right translates `κ ↦ det (κk)_{A,B}`,
  `k ∈ O(n)`, span a finite-dimensional space.
- `char_signUnit`: under `χ_l(1) = 1` and the sign condition for `A`, `χ_l(sgn y) = sgn y` for
  `l ∈ A` and `χ_l(sgn y) = 1` for `l ∉ A`.
- `minorFun_signDiagonal`: under the same hypotheses,
  `det (diag(sgn a) κ)_{A,B} = χδ^{1/2}(sgn a) · det κ_{A,B}` for `a : Fin n → ℝˣ`.

Minor vectors in the principal series:

- `minorVector n e A B = extension (shiftedExponent n e) (minorFun n A B)`. This is the function
  `φ_{A,B}` on `GL_n` from the Library's `PrincipalSeriesExtension.extension`.
- `minorVector_mem`: if `IsSignedPower χ e`, the sign condition for `A` holds and `|B| = |A|`,
  then `φ_{A,B}` is an `O(n)`-finite vector of the principal series of `χ`.
- `minorVector_of_mem`: `φ_{A,B}(k) = det k_{A,B}` for `k ∈ O(n)`. This holds for every `e`.
- `minorVector_mul`: under the hypotheses of `minorVector_mem`, for `g ∈ GL_n` and `k₀ ∈ O(n)`,
  `φ_{A,B}(g k₀) = ∑_{|C| = |A|} det (k₀)_{C,B} · φ_{A,C}(g)`.

Minors along the chart and of `diag(κ, 1)`:

- `chart_rows_eq_one`: the rows `i < m` of `J(x, 1)` are rows of the identity matrix.
- `minor_chart`: if `J(x, 1) = diag(a) u k` with `u` upper unipotent and `k ∈ O(m+1)`, then for
  `A ⊆ {0, …, m}`, `det k_{A,A} = (∏_{i∈A} a_i)^σ`, where `σ = 1` if `m ∉ A` and `σ = −1` if
  `m ∈ A`.
- `restrictSet A = A' = {i < m | i ∈ A}` for `A ⊆ {0, …, m}`, with `mem_restrictSet`.
  `map_restrictSet`: if `m ∉ A`, the image of `A'` under `Fin.castSucc` is `A`.
  `map_compl_restrictSet`: if `m ∈ A`, the image of the complement of `A'` is the complement of
  `A`.
- `submatrix_iota`: the upper-left `m × m` block of `ι(X)` is `X`.
- `minor_iota`: if `κ κᵀ = 1`, then `det ι(κ)_{A,A} = det κ_{A',A'}`.

The chart integrals, for `n = m + 1`:

- `principalSeriesCharacter_single`: under `χ_l(1) = 1` and the sign condition for `A`, the
  sign vector `t` with `t_{j₀} = −1` and `t_i = 1` for `i ≠ j₀` has `χδ^{1/2}(t) = −1` if
  `j₀ ∈ A` and `1` otherwise.
- `prod_single_sign`: `∏_{i∈C} t_i = −1` if `j₀ ∈ C` and `1` otherwise.
- `integral_minorVector_eq_zero`: if `IsSignedPower χ e`, the sign condition for `A` holds,
  `|C| = |A|` and `C ≠ A`, then `∫_{ℝ^m} φ_{A,C}(J(x, 1)) dx = 0`.
- `integral_minorVector_ne_zero`: if `IsSignedPower χ e`, `IsStrictlyDominant e m` and the sign
  condition for `A` holds, then `λ_A = ∫_{ℝ^m} φ_{A,A}(J(x, 1)) dx ≠ 0`.

One step and the recursion:

- `shiftChar_sign`: the sign condition for `A` implies the sign condition for `A'` for the
  shifted characters `χ''_l` with `l < m`.
- `jacquetStep_minorVector`: if `IsSignedPower χ e`, `IsStrictlyDominant e m` and the sign
  condition for `A ⊆ {0, …, m}` holds, then `T φ_{A,A} = λ_A · φ''_{A',A'}`. Here
  `φ''_{A',A'} = minorVector m (fun l => e l − 1/2) A' A'` is the minor vector on `GL_m`, for the
  exponents `e_l − 1/2` of `χ''`.
- `jacquet_minorVector_ne_zero` (**main theorem**): for every `n`, if `IsSignedPower χ e`,
  `IsStrictlyDominant e (n − 1)` and the sign condition for `A ⊆ {0, …, n−1}` holds, then
  `Λ_n(φ_{A,A}) ≠ 0`.

## Proof

1. **Minor functions** (`minorFun_mul`, `finiteDimensional_minorFun`, `minorFun_signDiagonal`).
   `minorFun_mul` is `MatrixMinor.minor_mul` (Cauchy–Binet). It writes every right translate of
   `minorFun n A B` as a combination of the finitely many functions `minorFun n A C`, so the
   span of the right translates is finite-dimensional. For `minorFun_signDiagonal`, the Library
   lemma `JacquetKernel.principalSeriesCharacter_sign` gives
   `χδ^{1/2}(sgn a) = ∏_l χ_l(sgn a_l)`. By `char_signUnit` this is `∏_{i∈A} sgn a_i`, which is
   the factor in `det (diag(sgn a) κ)_{A,B} = (∏_{i∈A} sgn a_i) det κ_{A,B}`
   (`minor_diagonal_mul`).
2. **Minor vectors** (`minorVector_mem`, `minorVector_of_mem`, `minorVector_mul`). Membership is
   the Library's `extension_mem_kFiniteFunctions`, applied with the continuity, finiteness and
   sign-equivariance of step 1. On `O(n)` the extension is the original function
   (`extension_unitary`). For `minorVector_mul`, write `g = diag(a) u k` (Iwasawa,
   `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`). Then
   `φ_{A,B}(g k₀) = χδ^{1/2}(a) det (k k₀)_{A,B}`. Expand by Cauchy–Binet and use
   `φ_{A,C}(g) = χδ^{1/2}(a) det k_{A,C}`.
3. **Principal minors along the chart** (`minor_chart`). Put `b = diag(a) u`, so
   `J(x, 1) = b k`. Since `J(−x, 1) J(x, 1) = 1` (`chartGL_mul_chartGL_neg`) and `k kᵀ = 1`,
   `kᵀ = J(−x, 1) b`. For `B` with `m ∉ B`, Cauchy–Binet gives
   `det k_{B,B} = det (kᵀ)_{B,B} = ∑_C det J(−x, 1)_{B,C} det b_{C,B}`. The rows of `J(−x, 1)`
   indexed by `B` are identity rows (`chart_rows_eq_one`), so only `C = B` survives
   (`minor_of_rows_eq_one`). Then `det b_{B,B} = ∏_{i∈B} a_i`, because `u` is upper
   unitriangular (`minor_diagonal_mul`, `minor_of_isUpperTriangular`). This is the case
   `m ∉ A`. If `m ∈ A`, Jacobi's complementary-minor identity
   (`minor_eq_det_mul_minor_compl`) gives `det k_{A,A} = det k · det k_{Aᶜ,Aᶜ}`, and
   `det k_{Aᶜ,Aᶜ} = ∏_{i∉A} a_i` by the first case. From `det J(x, 1) = 1` (`det_Jmat`) and
   `det u = 1` we get `(∏_i a_i) det k = 1`. Hence `det k_{A,A} = (∏_{i∈A} a_i)⁻¹`.
4. **Minors of `diag(κ, 1)`** (`minor_iota`). If `m ∉ A`, then `A` is the image of `A'`, and
   `MatrixMinor.minor_submatrix_castSucc` with `submatrix_iota` gives the claim. If `m ∈ A`,
   apply Jacobi's identity to `ι(κ)` (orthogonal, `det ι(κ) = det κ`) and to `κ`. The complement
   of `A` is the image of the complement of `A'`, so the first case applies to the complements.
5. **Off-diagonal chart integrals vanish** (`integral_minorVector_eq_zero`). Choose `i ∈ A ∖ C`
   and `c ∈ C ∖ A`; they are distinct, so one of them is some `j < m`. Then `j` lies in exactly
   one of `A`, `C`. Let `t` be the sign vector with `−1` exactly at `j`, and `D = diag(s)` with
   `s = (t_0, …, t_{m−1})`, so `ι(D) = diag(t)` (`iotaGL_diagonalUnits`). Compute
   `I = ∫ φ_{A,C}(J(x, 1) diag(t)) dx` in two ways.
   - `J(x, 1) ι(D) = ι(D) J(xD, 1)` (`chartGL_mul_iotaGL`), and the left `diag(t)` contributes
     `χδ^{1/2}(t) = ε_A` (principal-series equivariance and `principalSeriesCharacter_single`).
     The substitution `x ↦ xD` has `|det D| = 1` (`integral_vecMul_eq`). So `I = ε_A λ_C`, where
     `λ_C = ∫ φ_{A,C}(J(x, 1)) dx`.
   - `diag(t) ∈ O(m+1)`. By `minorVector_mul`, `minor_diagonal` and `prod_single_sign`,
     `φ_{A,C}(g diag(t)) = ε_C φ_{A,C}(g)`. So `I = ε_C λ_C`.

   Here `ε_A = −1` if `j ∈ A` and `1` otherwise, and likewise `ε_C`. Since `ε_A = −ε_C`, `λ_C = 0`.
6. **The diagonal chart integral** (`integral_minorVector_ne_zero`). Write
   `J(x, 1) = diag(a) u k` (Iwasawa). By equivariance, `minorVector_of_mem` and step 3,
   `φ_{A,A}(J(x, 1)) = χδ^{1/2}(a) (∏_{i∈A} a_i)^σ`. With `t = torusExponent e A σ`, the module
   `ChartIwasawaPower` turns this into `∏_l |a_l|^{t_l}`
   (`principalSeriesCharacter_mul_prod_zpow`) and then into
   `∏_{l<m} r_{l+1}(x)^{(t_{l+1} − t_l)/2}` (`prod_abs_cpow_chart`). These exponents satisfy the
   tail condition (`tailCondition_torusExponent`), so the integral is nonzero by
   `PartialSqIntegral.integrable_and_integral_prod_ne_zero`.
7. **One step** (`jacquetStep_minorVector`). Both sides lie in the principal series of `χ''`:
   the left side by the Library's `jacquetStep_mem`, the right side by `minorVector_mem` for
   `χ''` (`IsSignedPower.shift`, `shiftChar_sign`). So it suffices to compare them on `O(m)`
   (`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). For `k ∈ O(m)`, `minorVector_mul` with
   `k₀ = ι(k) ∈ O(m+1)` gives
   `T φ_{A,A}(k) = ∑_{|C| = |A|} det ι(k)_{C,A} · λ_C`. Each summand is integrable
   (`integrable_chart`), so the integral of the finite sum is the sum of the integrals. By step 5
   only `C = A` survives, and by step 4 `det ι(k)_{A,A} = det k_{A',A'} = φ''_{A',A'}(k)`.
8. **Recursion** (`jacquet_minorVector_ne_zero`), by induction on `n`. For `n = 0`, `A = ∅` and
   `Λ_0 φ_{∅,∅} = φ_{∅,∅}(1) = det of the empty minor = 1` (`minor_empty`). For `n = m + 1`,
   `Λ_{m+1} φ_{A,A} = Λ_m(T φ_{A,A}) = λ_A Λ_m(φ''_{A',A'})` by step 7 and
   `JacquetKernel.jacquet_smul`. Here `λ_A ≠ 0` by step 6. The second factor is nonzero by the
   induction hypothesis for `(χ'', e − 1/2, A')`: `χ''` is a signed power
   (`IsSignedPower.shift`), `e − 1/2` is strictly dominant up to `m − 1`
   (`JacquetDual.isStrictlyDominant_shift`), and the sign condition holds by `shiftChar_sign`.
