# The Jacquet integral of the spherical vector, and its cyclicity (strictly ordered case)

Lean module: `Langlands.Representation.Archimedean.ComplexSphericalJacquet`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. The operator (request
`08a6dcd43c545ecdb45b5e19f96ef9f4`) assigned the Library statement
`ComplexTemperedStandardIrreducibleStatement` (written U below) to Worker 728 (Task 7064), and
asked for supporting lemmas to be staged under Task 7063. Worker 728 and Worker 140 agreed that
this module is Worker 140's part "P2, strict case": the spherical vector is cyclic when the real
parts of the exponents strictly decrease. The tied ("face") case and the tempered core are
separate pieces of work.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ` and `U(n)` is `unitaryCompact ℂ n` (the
image of `Matrix.unitaryGroup (Fin n) ℂ` under `Unitary.toUnits`). For `x : Fin m → ℂ`,
`J(x,1) = chartGL x ∈ GL_{m+1}(ℂ)` is the identity matrix with its last row replaced by `(x, 1)`.
`r_l(x) = partialSq x l = 1 + ∑_{j<l} |x_j|²`. `ι : GL_m(ℂ) → GL_{m+1}(ℂ)`, `g ↦ diag(g, 1)`, is
`iotaGL`. Characters are `χ : ℕ → ℂˣ → ℂ` with exponents `e : ℕ → ℂ`; `IsPhasePower χ e` means
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, and `|χ_l(z/|z|)| = 1`. `IsStrictlyDominant e m`
means `Re e_{l+1} < Re e_l` for `l < m`. The partial Jacquet integral is
`jacquetStep h g = ∫_{ℂ^m} h(J(x,1) ι(g)) dx` (`ComplexPartialJacquet.jacquetStep`) and the
Jacquet integral is `Λ_0(h) = h(1)`, `Λ_{m+1}(h) = Λ_m(jacquetStep h)`
(`ComplexJacquetDual.jacquet`). Unprefixed names below are in
`Langlands.Archimedean.ComplexSphericalJacquet`.

## The statement

`Langlands.Archimedean.ComplexSphericalCyclicStatement`: for every `n` and every list `ds` of `n`
complex characters (`ComplexCharacterData`) such that

* every weight is `0`, so the `i`-th character is `z ↦ |z|^{2 t_i}` with `t_i = exponent`, and
* the real parts of the exponents strictly decrease along the list
  (`ds.Pairwise (fun d e => e.exponent.re < d.exponent.re)`, that is `Re t_i > Re t_j` for
  `i < j`),

and every `U(n)`-finite function `f₀` of `complexStandardModule n ds` with `f₀(κ) = 1` for all
`κ ∈ U(n)` (the spherical vector): every subspace `W` of the `U(n)`-finite functions of
`complexStandardModule n ds` that is stable under `complexStandardRep n ds k` for all
`k ∈ U(n)` and under `complexStandardLie n ds Z` for all `Z ∈ ℂ ⊗_ℝ M_n(ℂ)`, and contains `f₀`,
is everything (`W = ⊤`).

It is proved as `Langlands.Archimedean.complexSphericalCyclic`.

Provenance. Derived, internal infrastructure for the proof of U. It is the strictly ordered,
`GL_n(ℂ)` case of the classical fact that the spherical vector of a spherical principal series
with dominant parameter generates it. No literature statement is cited or claimed: the
statement is exactly the Lean proposition above, and the proof is self-contained over the Library.

## Proof

### The rank-one integral

`integral_add_norm_sq_cpow`: for `A > 0` and `Re σ < -1`,
`∫_ℂ (A + |y|²)^σ dy = -π A^{σ+1}/(σ+1)`. Polar coordinates (`integral_fun_norm_addHaar`, the
unit disc has area `π`) reduce it to `2π ∫_0^∞ r (A + r²)^σ dr`. The substitution `t = r²`
(`integral_comp_rpow_Ioi_of_pos`) and then the shift `u = A + t` turn it into
`π ∫_A^∞ u^σ du = -π A^{σ+1}/(σ+1)` (`integral_Ioi_cpow_of_lt`).

### The iterated chart integral

`chartFun m s w y = r_m(y)^w ∏_{l<m} r_{l+1}(y)^{s_l}` for `s : Fin m → ℂ`, `w : ℂ`,
`y : Fin m → ℂ` (complex powers of positive reals).

* `norm_chartFun`, `measurable_chartFun`, `integrable_chartFun`: its norm is the real function
  with exponents `Re s_l`, `Re w`, so it is integrable under the Library's `TailCondition`
  (`ComplexPartialSqIntegral.integrable_partialSq_mul_prod`).
* `chartFun_snoc`: since `r_{m+1}(y, t) = r_m(y) + |t|²`,
  `chartFun (m+1) s w (y, t) = (r_m(y) + |t|²)^{w + s_m} ∏_{l<m} r_{l+1}(y)^{s_l}`.
* `tail_last`, `tail_castSucc`: the tail condition gives `Re(w + s_m) < -1` and passes to
  `(s_0, …, s_{m-1})`, `w + s_m + 1`.
* `integral_chartFun_succ`: Fubini over `ℂ^{m+1} = ℂ × ℂ^m` (`volume_preserving_piFinSuccAbove`,
  `integral_prod_symm`) and the rank-one integral with `A = r_m(y)` give
  `∫ chartFun (m+1) s w = -π/(w + s_m + 1) · ∫ chartFun m (s_0, …, s_{m-1}) (w + s_m + 1)`.
* `integral_chartFun_ne_zero`: under the tail condition the integral is nonzero, by induction on
  `m` (`m = 0`: the integral over a point is `1`; step: `π ≠ 0` and `w + s_m + 1 ≠ 0` because its
  real part is negative).

### The spherical vector along the chart

Assume `IsPhasePower χ e` and `χ_l(z/|z|) = 1` for all `l`, `z`.

* `sum_mul_eq_sum_sub_complex` (summation by parts): if `T_l = ∑_{j ≥ l} t_j` and `T_0 = 0`, then
  `∑_{l ≤ m} σ_l t_l = ∑_{l<m} (σ_{l+1} - σ_l) T_{l+1}`.
* `ofReal_cpow_eq_exp`: `r^z = exp(z log r)` for `r > 0`.
* `principalSeriesCharacter_chart`: if `J(x,1) = diag(a) u k` (Iwasawa decomposition, `u` upper
  unipotent, `k ∈ U(m+1)`), then
  `principalSeriesCharacter ℂ (m+1) χ a = ∏_{l<m} r_{l+1}(x)^{e_{l+1} - e_l - 1}`. The left side is
  `exp(∑_l σ_l t_l)` with `t_l = log |a_l|²` and `σ_l = e_l + m/2 - l`. The Library's
  `ComplexParabolicChartBound.prod_tail_sq_eq` gives `T_l = ∑_{j ≥ l} t_j = log r_l(x)` for
  `l ≤ m`, so `T_0 = log 1 = 0`. Summation by parts with `σ_{l+1} - σ_l = e_{l+1} - e_l - 1`
  gives the right side.
* `apply_mul_unitary`: if `T` is in the principal series and `T(k) = T(1)` on `U(n)`, then
  `T(g κ) = T(g)` for `κ ∈ U(n)` (Iwasawa decomposition of `g`).
* `apply_chartGL`: for such `T` on `GL_{m+1}(ℂ)`,
  `T(J(x,1)) = T(1) · chartFun m (l ↦ e_{l+1} - e_l - 1) 0 x`.
* `jacquetStep_unitary`, `jacquetStep_one`: `jacquetStep T` is again constant on `U(m)`
  (`ι(k) ∈ U(m+1)`), with value `jacquetStep T 1 = T(1) ∫ chartFun m (l ↦ e_{l+1} - e_l - 1) 0`.
* `tailCondition_chart`: for strictly dominant `e`, every exponent `Re(e_{l+1} - e_l - 1)` is
  `< -1`, so the tail condition holds with `w = 0`
  (`ComplexPartialSqIntegral.tailCondition_of_le`; vacuous for `m = 0`).

### Nonvanishing of the Jacquet integral

`jacquet_ne_zero`: if `IsPhasePower χ e`, `IsStrictlyDominant e (n-1)`, `χ_l(z/|z|) = 1` for all
`l`, `z`, and `T` is a `U(n)`-finite function of `principalSeries ℂ n χ` with `T(k) = T(1)` on
`U(n)` and `T(1) ≠ 0`, then `ComplexJacquetDual.jacquet n T ≠ 0`. Induction on `n`: for `n = 0`,
`Λ_0(T) = T(1)`. For `n = m + 1`, `Λ_{m+1}(T) = Λ_m(jacquetStep T)`. Here `jacquetStep T` is a
`U(m)`-finite function of the principal series of the shifted characters
(`ComplexPartialJacquet.jacquetStep_mem`; `IsPhasePower.shift`,
`ComplexJacquetDual.isStrictlyDominant_shift`). The shifted characters are still trivial on
phases. `jacquetStep T` is constant on `U(m)` with nonzero value
`T(1) ∫ chartFun … ≠ 0` (`integral_chartFun_ne_zero`), so the induction hypothesis applies.

### Weight-zero lists, and the closed statement

* `complexPositionWeight_eq_zero`: if every weight of `ds` is `0`, every
  `complexPositionWeight ds l` is `0`. So, by
  `ComplexStrictLanglandsQuotient.complexPositionCharacter_phase`, the characters
  `complexPositionCharacter ds` are trivial on phases.
* `complexSphericalCyclic`. The characters `complexPositionCharacter ds` are phase powers
  (`ComplexStrictLanglandsQuotient.isPhasePower`) with strictly dominant exponents
  (`ComplexStrictLanglandsQuotient.isStrictlyDominant`). Suppose `W ≠ ⊤` and pick `g ∉ W`. The
  image of `W` in the function space is stable under right translation by `U(n)` and under the
  right derivatives, and does not contain `g`. So
  `ComplexJacquetKernel.jacquet_eq_zero_of_proper` puts it in the kernel of the Jacquet
  integral, giving `Λ_n(f₀) = 0`. But `f₀ = 1` on `U(n)`, so `jacquet_ne_zero` gives
  `Λ_n(f₀) ≠ 0`, a contradiction.
