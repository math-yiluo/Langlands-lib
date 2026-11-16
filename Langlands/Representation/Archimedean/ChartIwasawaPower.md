# Powers of the Iwasawa torus coordinates along the chart `J(x, 1)`

Lean module: `Langlands.Representation.Archimedean.ChartIwasawaPower`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It sits between `PartialSqIntegral` and
`JacquetMinorNonvanishing`. Take a real principal series of signed-power characters and a
principal minor vector in it. This module rewrites that vector, restricted to the chart
`x ↦ J(x, 1)` of the opposite unipotent radical of `P_{m,1}`, as a product of complex powers of
the Gram determinants `r_l(x)`. It then shows that strict dominance of the exponents gives the
tail condition of `PartialSqIntegral`.

Notation. `x ∈ ℝ^m`, `J(x, 1)` is `MaximalParabolicIntegration.chartGL x ∈ GL_{m+1}(ℝ)`, and `r_l(x) = partialSq x l = 1 + ∑_{j<l} x_j²`
(`ParabolicChartBound.partialSq`). An Iwasawa decomposition `J(x, 1) = diag(a) u k` has
`a : Fin (m+1) → ℝˣ`, `u` upper unipotent and `k ∈ O(m+1)` (`unitaryCompact ℝ (m+1)`). For
characters `χ_l` of `ℝˣ`, the modular character of `principalSeriesCharacter ℝ N χ` is
`χδ^{1/2}(a) = ∏_l χ_l(a_l) |a_l|^{(N−1)/2 − l}`. `IsSignedPower χ e` means
`χ_l(y) = χ_l(sgn y) |y|^{e_l}` with `χ_l(1) = 1` and `|χ_l(−1)| = 1`.
`IsStrictlyDominant e m` means `Re e_{l+1} < Re e_l` for `l < m`. Complex powers of positive reals
are `Complex.cpow`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.ChartIwasawaPower`.

Provenance. This is derived internal infrastructure with no literature source. The facts are
elementary: Abel summation, the Gram-determinant formula for the Iwasawa torus coordinates of
`J(x, 1)` (proved in the Library as `ParabolicChartBound.prod_tail_sq_eq`), and bookkeeping of
real parts. The module makes no literature claim.

## Main results

- `tailProd α l = ∏_{j ≥ l} α_j` for `α : Fin N → ℝ`. Lemmas: `tailProd_succ` (shift),
  `tailProd_zero` (`ρ_0 = α_0 ρ_1`), `tailProd_pos`.
- `prod_cpow_eq_tailProd` (Abel summation): for positive `α_0, …, α_m` and complex `t`,
  `∏_l α_l^{t_l} = ρ_0^{t_0} ∏_{l<m} ρ_{l+1}^{t_{l+1} − t_l}`, where `ρ_l = tailProd α l`.
- `tailProd_abs_chart`: if `J(x, 1) = diag(a) u k` with `k ∈ O(m+1)`, then
  `∏_{j ≥ l} |a_j| = √(r_l(x))` for `l ≤ m`.
- `prod_abs_cpow_chart`: under the same hypothesis, for every `t : Fin (m+1) → ℂ`,
  `∏_l |a_l|^{t_l} = ∏_{l<m} r_{l+1}(x)^{(t_{l+1} − t_l)/2}`.
- `signUnit_of_pos`, `signUnit_of_neg`: `sgn y = 1` for `y > 0` and `sgn y = −1` for `y < 0`
  (`GramFormula.signUnit`).
- `char_mul_zpow_odd`: if `χ_l(y) = χ_l(sgn y) |y|^{e_l}`, `χ_l(1) = 1`, `χ_l(−1) = −1` and
  `σ = ±1`, then `χ_l(y) y^σ = |y|^{e_l + σ}`.
- `char_eq_abs_cpow_even`: under the same identity with `χ_l(1) = χ_l(−1) = 1`,
  `χ_l(y) = |y|^{e_l}`.
- `torusExponent e I σ l = e_l + (N−1)/2 − l + σ·[l ∈ I]` for `I ⊆ {0, …, N−1}`, `σ ∈ ℤ`.
- `principalSeriesCharacter_mul_prod_zpow`: if `IsSignedPower χ e`, `χ_l(−1) = −1` for `l ∈ I`
  and `χ_l(−1) = 1` for `l ∉ I`, and `σ = ±1`, then for every `a : Fin N → ℝˣ`
  `χδ^{1/2}(a) · (∏_{i∈I} a_i)^σ = ∏_l |a_l|^{torusExponent e I σ l}`.
- `re_lt_of_lt`: if `IsStrictlyDominant e m`, then `Re e_k < Re e_j` for `j < k ≤ m`.
- `tailCondition_torusExponent`: if `IsStrictlyDominant e m`, `I ⊆ {0, …, m}`, and `σ = −1` when
  `m ∈ I` and `σ = 1` when `m ∉ I`, then the exponents
  `d_l = (t_{l+1} − t_l)/2` (`l < m`) with `t = torusExponent e I σ` satisfy
  `PartialSqIntegral.TailCondition d 0`, i.e. `∑_{l ≥ j} (Re d_l + 1/2) < 0` for every `j < m`.

## Proof

1. **Abel summation** (`prod_cpow_eq_tailProd`), by induction on `m`. For `m = 0` both sides are
   `α_0^{t_0}`. For `m + 1`, peel off the factor `l = 0` (`Fin.prod_univ_succ`) and apply the
   induction hypothesis to `(α_1, …, α_{m+1})` and `(t_1, …, t_{m+1})`; its tail products are
   `ρ_1, ρ_2, …` (`tailProd_succ`). It remains to see
   `α_0^{t_0} ρ_1^{t_1} = ρ_0^{t_0} ρ_1^{t_1 − t_0}`. This holds since `ρ_0 = α_0 ρ_1`
   (`tailProd_zero`), `(α_0 ρ_1)^{t_0} = α_0^{t_0} ρ_1^{t_0}` for positive reals
   (`Complex.mul_cpow_ofReal_nonneg`) and `ρ_1^{t_1} = ρ_1^{t_0} ρ_1^{t_1 − t_0}`
   (`Complex.cpow_add`, `ρ_1 > 0`).
2. **Tail products along the chart** (`tailProd_abs_chart`). The Library lemma
   `ParabolicChartBound.prod_tail_sq_eq` (with `κ = 1`) gives `(∏_{j ≥ l} a_j)² = r_l(x)` for
   `l ≤ m`. Taking square roots, `|∏_{j ≥ l} a_j| = ∏_{j ≥ l} |a_j| = √(r_l(x))`.
3. **Torus powers along the chart** (`prod_abs_cpow_chart`). Apply step 1 to `α_j = |a_j| > 0`. By
   step 2, `ρ_0 = √(r_0) = 1`, so the first factor is `1`. Also
   `ρ_{l+1} = √(r_{l+1}) = r_{l+1}^{1/2}`, so
   `ρ_{l+1}^{t_{l+1} − t_l} = r_{l+1}^{(t_{l+1} − t_l)/2}` (`Complex.cpow_mul_ofReal_nonneg`).
4. **Odd and even characters** (`char_mul_zpow_odd`, `char_eq_abs_cpow_even`). Split on the sign
   of `y`. If `y > 0`, then `χ_l(sgn y) = χ_l(1) = 1`, `|y| = y` and `y^σ = |y|^σ`. If `y < 0`, then
   `χ_l(sgn y) = χ_l(−1)`. In the odd case `χ_l(−1) = −1` cancels the sign of `y^σ = −|y|^σ`
   (`σ = ±1`); in the even case `χ_l(−1) = 1`. Finally `|y|^{e_l} |y|^σ = |y|^{e_l + σ}`
   (`Complex.cpow_add`, `Complex.cpow_intCast`).
5. **The character times the monomial** (`principalSeriesCharacter_mul_prod_zpow`). Write
   `(∏_{i∈I} a_i)^σ = ∏_l (a_l^σ if l ∈ I, else 1)` (`Finset.prod_zpow`, `Finset.prod_filter`)
   and combine the two products factor by factor. For `l ∈ I`, step 4 (odd) gives
   `χ_l(a_l) a_l^σ |a_l|^{(N−1)/2 − l} = |a_l|^{e_l + σ + (N−1)/2 − l}`. For `l ∉ I`, step 4
   (even) gives `χ_l(a_l) |a_l|^{(N−1)/2 − l} = |a_l|^{e_l + (N−1)/2 − l}`.
6. **Strict dominance** (`re_lt_of_lt`), by induction on `k`, chaining
   `Re e_{l+1} < Re e_l`.
7. **The tail condition** (`tailCondition_torusExponent`). For `m = 0` there is no `j`. Otherwise
   put `F(l) = Re t_l / 2 + l/2`, so `Re d_l + 1/2 = F(l+1) − F(l)`. The tail sum over
   `j ≤ l < m` telescopes (`Fin.sum_Icc_sub`) to `F(m) − F(j)`, which equals
   `(Re e_m − Re e_j)/2 + (σ[m ∈ I] − σ[j ∈ I])/2`. The first term is negative by step 6. The
   second term is `≤ 0` in each of the four cases `m ∈ I` or not, `j ∈ I` or not, by the choice
   of `σ`. So the sum is negative.
