# Proof of the moment formulas for the `GL_2(ℂ)` principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoMomentJacquetProof`. The theorem
`Langlands.Archimedean.complexGLTwoMomentJacquet : ComplexGLTwoMomentJacquetStatement` proves
the statement of `ComplexGLTwoJacquetOrderingReduction`. The helper lemmas are in the namespace
`Langlands.Archimedean.ComplexGLTwoMoment`. The proof uses the chart and Lie formulas of
`ComplexSwapJacquet` (`ComplexSwapJacquetChart`, `ComplexSwapJacquetDecay`,
`ComplexSwapJacquetFunctional`, `ComplexSwapJacquetProof`) and the weighted
integration-by-parts identities of `ComplexGLTwoMomentAnalysis`.

## Statement being proved

Let `d 0`, `d 1` be complex characters with exponents `t_0`, `t_1` and weights `l_0`, `l_1`,
and let `X(d)` be the `U(2)`-finite functions of the standard module of `List.ofFn d`. Write
`w = [[0, 1], [1, 0]]`, `n(z) = [[1, z], [0, 1]]` and
`M_{i,j} f = ∫_ℂ f(w n(z)) z^i z̄^j dz`. If `i + j < 2 Re(t_0 - t_1)` and `f ∈ X(d)`, then:

1. `z ↦ f(w n(z)) z^i z̄^j` is integrable;
2. for `X` strictly upper triangular,
   `M_{i,j}(R(X) f) = -(i X₀₁ M_{i-1,j} f + j X̄₀₁ M_{i,j-1} f)`;
3. `M_{i,j}(R(E_kk) f) = a'_k M_{i,j} f` and `M_{i,j}(R(i E_kk) f) = b'_k M_{i,j} f`, with
   `a' = (2 t_1 + 1 + (i + j), 2 t_0 - 1 - (i + j))` and
   `b' = (i (l_1 + i - j), i (l_0 - i + j))`.

## Decay along the chart

* `rpow_neg_le_two_rpow_mul` and `one_le_two_rpow_mul`: for `r ≥ 0`, `x^(-r) ≤ 2^r (1 + x)^(-r)`
  when `x ≥ 1`, and `1 ≤ 2^r (1 + x)^(-r)` when `0 ≤ x ≤ 1`.
* `exists_bound_chart_rpow`: for `h` in the standard module of `pre ++ d :: e :: post`, with
  `d`, `e` at the chart positions `i`, `j = i + 1` and `Re(t_d - t_e) ≥ 0`, there is `C` with
  `|h(s x(z))| ≤ C (1 + |z|)^(-(2 + 2 Re(t_d - t_e)))` for all `z`, where `s x(z)` is
  `ComplexSwapJacquet.chart i j hj z`. Proof: for `|z| ≤ 1` bound `h(s x(z))` by its maximum on
  the unit disc (`exists_bound_ball`, `contDiff_apply_chart`). For `|z| ≥ 1`, `apply_chart_eq`
  writes `h(s x(z))` as the character at the torus element `chartTorus i j z` times
  `h(lowerChart i j hj z⁻¹)`. The character has absolute value `|z|^(-2 - 2 Re(t_d - t_e))`
  (`norm_principalSeriesCharacter_chartTorus`), and the second factor is bounded on the unit
  disc (`contDiff_apply_lowerChart`). The constant is `2^r (M + M')`, with
  `r = 2 + 2 Re(t_d - t_e)` and `M`, `M'` the two disc bounds.

## The chart for `n = 2`

* `hj01`: the positions `0, 1` of `Fin 2` are adjacent.
* `weyl_mul_unipotent`: `w n(z) = ComplexSwapJacquet.chart 0 1 hj01 z`, checked entrywise
  (`chart_val`: the chart is `swap 0 1 * transvection 0 1 z`).
* `ofFn_eq`: `List.ofFn d = [] ++ d 0 :: d 1 :: []`, which puts `List.ofFn d` in the shape used
  by `exists_bound_chart_rpow`.
* `kappa_ofFn_one`: `κ_k(1) = 2 t_k + 1 - 2k`, and `kappa_ofFn_I`: `κ_k(i) = i l_k`. These are
  `kappa_one` and `kappa_I` for `n = 2`.

## Bounds along the chart

Write `φ(z) = f(s x(z))` with `s x(z) = w n(z)` the chart at positions `0, 1`, and
`a = 2 + 2 Re(t_0 - t_1)`.

* `moment_eq`: `M_{i,j} g = ∫ g(s x(z)) · weight i j z` for every function `g`
  (`weyl_mul_unipotent` and associativity).
* `exists_bound_module`: every `g` in the standard module of `List.ofFn d` satisfies
  `|g(s x(z))| ≤ C (1 + |z|)^(-a)` when `Re(t_0 - t_1) ≥ 0` (`exists_bound_chart_rpow` with
  `pre = post = []`).
* `bound_mono`: `x ≤ C p`, `C ≤ C'`, `0 ≤ p` give `x ≤ C' p`.
* `exists_bounds`: for `f` in the standard module and `Re(t_0 - t_1) ≥ 0`, one constant `C`
  bounds `φ(z)`, `Dφ(z) 1`, `Dφ(z) i`, `Dφ(z) z` and `Dφ(z)(i z)` by `C (1 + |z|)^(-a)`. Each
  quantity is the value along the chart of a function in the standard module (the module is
  stable under right derivatives, `rightDerivative_mem_principalSeries`):
  * `Dφ(z)(c) = R(c E₀₁) f (s x(z))` (`ChartLieFacts.single_ij`), for `c = 1, i`;
  * `Dφ(z)(c z) = (R(c E₁₁) f - κ_0(c) f)(s x(z))` (`ChartLieFacts.diag_j`), for `c = 1, i`.

  `exists_bound_module` bounds each of the five, and the common constant is the maximum of
  the five constants.
* `integral_mul_weight_eq`: if `ψ = κ φ + s D` pointwise and `φ p`, `D p` are integrable, then
  `∫ ψ p = κ ∫ φ p + s ∫ D p`.

## The main theorem

`complexGLTwoMomentJacquet`. Let `f ∈ X(d)` and `i + j < 2 Re(t_0 - t_1)`. Then
`Re(t_0 - t_1) ≥ 0` and `i + j + 2 < a`. `exists_bounds` gives the five bounds, `chartLieFacts`
gives the chart formulas at positions `0, 1`, and `φ` is `C¹` (`contDiff_one_chart`).
`integrable_mul_weight` and `integrable_fderiv_apply_mul_weight` show that `φ p`, `Dφ(z)(z) p`
and `Dφ(z)(i z) p` are integrable.

1. **Integrability**: the integrand `f(w n(z)) z^i z̄^j` equals `φ(z) p(z)`.
2. **Upper nilpotent part**: for strictly upper triangular `X`,
   `R(X) f (s x(z)) = R(X - X₀₁ E₀₁) f (s x(z)) + R(X₀₁ E₀₁) f (s x(z)) = 0 + Dφ(z)(X₀₁)`.
   This uses `ComplexSwapJacquet.rightDerivative_add`, `ChartLieFacts.strictUpper` (the
   matrix `X - X₀₁ E₀₁` is strictly upper triangular with vanishing `(0, 1)` entry,
   `strictUpper_sub_single`) and `ChartLieFacts.single_ij`. After `moment_eq`, the
   translation identity `integral_fderiv_mul_weight` with `c = X₀₁` is the claimed formula.
3. **Diagonal part**: the four cases `k ∈ {0, 1}`, `c ∈ {1, i}` (`Fin.forall_fin_two`).
   * `k = 0`: `R(c E₀₀) f (s x(z)) = κ_1(c) φ(z) - Dφ(z)(c z)` (`ChartLieFacts.diag_i`). By
     `integral_mul_weight_eq`, `M_{i,j}(R(c E₀₀) f) = κ_1(c) M_{i,j} f - ∫ Dφ(z)(c z) p`.
     For `c = 1`, Euler (`integral_fderiv_self_mul_weight`) gives
     `(2 t_1 - 1) + (2 + i + j) = 2 t_1 + 1 + (i + j)`. For `c = i`, rotation
     (`integral_fderiv_I_mul_self_mul_weight`) gives `i l_1 + i (i - j) = i (l_1 + i - j)`.
   * `k = 1`: `R(c E₁₁) f (s x(z)) = κ_0(c) φ(z) + Dφ(z)(c z)` (`ChartLieFacts.diag_j`), so
     `M_{i,j}(R(c E₁₁) f) = κ_0(c) M_{i,j} f + ∫ Dφ(z)(c z) p`. For `c = 1` this is
     `(2 t_0 + 1) - (2 + i + j) = 2 t_0 - 1 - (i + j)`, and for `c = i` it is
     `i l_0 - i (i - j) = i (l_0 - i + j)`.

   The values of `κ` come from `kappa_ofFn_one` and `kappa_ofFn_I`. The remaining identities
   are ring arithmetic.
