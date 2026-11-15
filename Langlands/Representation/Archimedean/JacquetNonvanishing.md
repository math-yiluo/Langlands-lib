# The Jacquet integral does not vanish on strictly dominant principal series

Lean module: `Langlands.Representation.Archimedean.JacquetNonvanishing`.

Let `χ` be a strictly dominant signed power on `GL_n(ℝ)` with sign values
`χ_l(−1) = (−1)^{p_l}`. This module shows that the Jacquet integral `Λ_n`
(`JacquetDual.jacquet`) is a nonzero functional on the `O(n)`-finite principal series
(`exists_jacquet_ne_zero`). More precisely, some sign vector has nonzero Jacquet integral
(`exists_jacquet_signVector_ne_zero`).

Declarations without a prefix are in the namespace `Langlands.Archimedean.JacquetNonvanishing`.

## Continuity of `Λ_n`

`tendsto_jacquet`: let `f_N, f₀` be in the `O(n)`-finite principal series of `χ`. Suppose
`‖f_N‖ ≤ C` on `O(n)` for every `N`, and `f_N → f₀` pointwise on `O(n)`. Then
`Λ_n(f_N) → Λ_n(f₀)`. The proof is by recursion on `n`. At each step `T f_N → T f₀` pointwise on
`O(m)` by dominated convergence, with the dominating function from
`PartialJacquet.norm_le_of_mem_principalSeries`. The pointwise convergence on chart points
`y = diag(a) u κ` follows from `f_N(y) = χδ^{1/2}(a) f_N(κ)`. The bound
`‖T f_N‖ ≤ C ∫ (dominating function)` holds on `O(m)`.

## Sign vectors

* `signMonomial n p a κ = ∏_l κ_ll^{p_l + 2 a_l}` on `O(n)`, for exponents `a : ℕ → ℕ`. It is
  continuous, and it is `O(n)`-finite by `TranslateFinite.finiteDimensional_span_eval`. Under
  diagonal sign matrices it transforms by the character of `χ` (`signMonomial_signDiagonal`),
  because `sgn^{p_l + 2a_l} = χ_l(sgn)`.
* `signVector n e p a` is its extension to the principal series of `χ`
  (`PrincipalSeriesExtension.extension`). It lies in the `O(n)`-finite principal series
  (`signVector_mem`) and equals the monomial on `O(n)` (`signVector_of_mem`).
* `signVector_iota`: `signVector (m+1) e p a (ι(k)) = signVector m e' p a (k)` for
  `k ∈ O(m)` and any `e'`.
* `qFun y = y_{mm}² / ∑_j y_{mj}²` is left invariant under the upper triangular Borel subgroup
  (`qFun_mul`). It equals `κ_mm²` on `O(m+1)` (`qFun_of_mem`), and `(1 + |x|²)⁻¹` at
  `J(x,1) ι(k)` for `k ∈ O(m)` (`qFun_chart`).
* `signVector_bump`: raising the last exponent by `N` (`bump a m N`) multiplies the sign vector
  by `q^N` on all of `GL_{m+1}(ℝ)`. Both sides transform by `χδ^{1/2}` on the left and agree on
  `O(m+1)`.

## The approximate identity

`tendsto_concentrate`: for `H` in the principal series of `χ`, `k ∈ O(m)` and `N' = N + m + 1`,

`N'^{m/2} ∫_{ℝ^m} (1 + |x|²)^{−N'} H(J(x,1) ι(k)) dx → (∫ e^{−|y|²} dy) · H(ι(k))`.

* The substitution `x = N'^{−1/2} y` (`integral_scale`, from `Measure.integral_comp_smul`) turns
  the left side into `∫ (1 + |y|²/N')^{−N'} H(J(N'^{−1/2}y,1)ι(k)) dy`.
* Pointwise, `(1 + s/N')^{N'} → e^s` (`Real.tendsto_one_add_div_pow_exp`) and
  `J(N'^{−1/2}y, 1) → 1`.
* Domination comes from Bernoulli's inequality (`bernoulli_pow`, from Mathlib's
  `one_add_mul_self_le_rpow_one_add`): `(1 + s/(m+1))^{m+1} ≤ (1 + s/N')^{N'}`. The function
  `y ↦ (1 + |y|²/(m+1))^{−(m+1)}` is integrable on `ℝ^m` (`integrable_inv_one_add_div_pow`, by
  comparison with `integrable_rpow_neg_one_add_norm_sq`). Also `‖H‖ ≤ C` at chart points
  (`norm_chart_le_of_mem`).

`norm_concentrate_le` gives the corresponding uniform bound.

## Nonvanishing

`exists_jacquet_signVector_ne_zero`, by recursion on `n`.

* `n = 0`. The sign vector is `1`, and `Λ_0` is evaluation at `1`.
* `n = m + 1`. The recursion hypothesis for `χ|·|^{−1/2}` (same signs) gives exponents `a` with
  `Λ_m(signVector m e'' p a) ≠ 0`. Put
  `F_N = N'^{m/2} · signVector (m+1) e p (bump a m N')`. On `O(m)`,
  `T F_N(k) = N'^{m/2} ∫ (1+|x|²)^{−N'} signVector (m+1) e p a (J(x,1)ι(k)) dx` (by
  `signVector_bump` and `qFun_chart`). By the approximate identity and `signVector_iota`, this
  converges boundedly to `c · signVector m e'' p a (k)`, with
  `c = ∫ e^{−|y|²} dy > 0`. By `tendsto_jacquet`,
  `Λ_{m+1}(F_N) = Λ_m(T F_N) → c Λ_m(signVector m e'' p a) ≠ 0`. So `Λ_{m+1}(F_N) ≠ 0` for some
  `N`, and by `jacquet_smul` the sign vector with exponents `bump a m N'` has nonzero Jacquet
  integral.
