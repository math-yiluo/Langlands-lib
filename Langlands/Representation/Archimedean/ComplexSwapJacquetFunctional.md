# The rank-one Jacquet functional of a complex principal series

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetFunctional`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source. It imports
`ComplexSwapJacquetAnalysis`, `ComplexSwapJacquetDecay` and the Library module
`ComplexJacquetReduction` (for `IsComplexJacquetFunctional`).

Fix a list `ds` of complex character data with `hn : ds.length = n` and adjacent positions
`i`, `j` (`hj : (j : ℕ) = i + 1`). Write `R(X)` for the right derivative, `s x(z)` for
`chart i j hj z`, `κ_k(c)` for `kappa ds hn k c`, and `φ_h(z) = h(s x(z))`. `KFs n ds` is the
space of `U(n)`-finite functions in `complexStandardModule n ds` (the same
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` that carries the
`(𝔤𝔩_n(ℂ), U(n))`-module structure `complexStandardLie n ds`).

## Hypothesis packages

The module does not prove the pointwise chart formulas. It takes them as a hypothesis structure,
so that it compiles independently of the module `ComplexSwapJacquetLie`, which proves them
(`ComplexSwapJacquetProof.chartLieFacts`).

* `ChartLieFacts ds hn i j hj` (a `Prop` structure): for every `f` in
  `complexStandardModule n ds`,
  * `single_ij`: `R(w E_ij) f (s x(z)) = Dφ_f(z)(w)`;
  * `strictUpper`: `R(X) f (s x(z)) = 0` for `X` strictly upper triangular with `X_ij = 0`;
  * `diag_other`: `R(c E_kk) f (s x(z)) = κ_k(c) f(s x(z))` for `k ∉ {i, j}`;
  * `diag_j`: `R(c E_jj) f (s x(z)) = κ_i(c) f(s x(z)) + Dφ_f(z)(c z)`;
  * `diag_i`: `R(c E_ii) f (s x(z)) = κ_j(c) f(s x(z)) - Dφ_f(z)(c z)`;
  * `one_strictUpper`: `R(X) f (1) = 0` for `X` strictly upper triangular;
  * `one_diag`: `R(c E_kk) f (1) = κ_k(c) f(1)`.
* `ChartDecay ds i j hj` (a `Prop` definition): every `h` in `complexStandardModule n ds`
  satisfies `‖h(s x(z))‖ ≤ C (1 + ‖z‖)⁻¹` for some `C`, and, if `h(1) = 0`,
  `‖h(s x(z))‖ ≤ C ((1 + ‖z‖)^3)⁻¹` for some `C`.
* `chartDecay pre post d e i j hi hj hre`: `ChartDecay` holds for `ds = pre ++ d :: e :: post`
  at `i = |pre|`, `j = i + 1`, when `0 ≤ Re(t_d - t_e)`. This is `exists_bound_chart` and
  `exists_bound_chart_of_eq_zero` from `ComplexSwapJacquetDecay`.

## Generalities

* `mem_of_mem_kFs`: `U(n)`-finite functions lie in the standard module.
* `coe_lie`: `complexStandardLie n ds (1 ⊗ X) v` is the function `R(X) v`
  (`principalSeriesLie_one_tmul_apply_coe`).
* `rightDerivative_add`: `R(X + Y) f (g) = R(X) f (g) + R(Y) f (g)`.
* `lie_comm`: `π(1 ⊗ A) π(1 ⊗ X) v = π(1 ⊗ X) π(1 ⊗ A) v + π(1 ⊗ (A X - X A)) v` for
  `π = complexStandardLie n ds`. It is `LieHom.map_lie` with the bracket of the scalar
  extension (`LieAlgebra.ExtendScalars.bracket_tmul`) and the commutator bracket of matrices.
* `clm_apply_eq`: a real-linear `L : ℂ →L[ℝ] ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
* `strictUpper_single`, `strictUpper_sub_single`, the imported `single_mul_strict_sub_mem`, `single_commute`:
  `w E_ij` is strictly upper triangular. If `X` is strictly upper triangular, so are
  `X - X_ij E_ij` and `c E_jj X - X c E_jj`. Diagonal matrix units commute.

## Integrals along the chart

From here on `LF : ChartLieFacts ds hn i j hj` and `hD : ChartDecay ds i j hj`.

* `integrable_chart_of_eq_zero`: `φ_h` is integrable when `h(1) = 0` (decay `(1 + ‖z‖)⁻³`,
  `integrable_of_bound`). `contDiff_one_chart`: `φ_h` is `C¹`.
* `integrable_rightDerivative_chart`, `integral_rightDerivative_chart`: for `X` strictly upper
  triangular, `z ↦ R(X) h (s x(z))` is integrable and has integral `0`. Proof: `R(X) h` lies in
  the principal series (`rightDerivative_mem_principalSeries`) and vanishes at `1`
  (`one_strictUpper`), which gives integrability. By `rightDerivative_add`, `strictUpper` and
  `single_ij`,
  `R(X) h (s x(z)) = Re X_ij · Dφ_h(z) 1 + Im X_ij · Dφ_h(z) i`.
  Both terms integrate to `0` by `integral_fderiv_one_eq_zero` and `integral_fderiv_I_eq_zero`:
  `φ_h → 0` at infinity by the `(1 + ‖z‖)⁻¹` decay.
* `exists_bound_fderiv_mul`, `integrable_fderiv_mul`: if `g(1) = 0`, then
  `‖Dφ_g(z)(c z)‖ ≤ C ((1 + ‖z‖)^3)⁻¹`, and this function is integrable. Proof:
  `h = R(c E_jj) g - κ_i(c) g` lies in the principal series. It satisfies
  `h(1) = (κ_j(c) - κ_i(c)) g(1) = 0` (`one_diag`), and `h(s x(z)) = Dφ_g(z)(c z)` (`diag_j`).
  Apply the decay to `h`.
* `exists_common_bound`: one constant for both bounds.
* `integral_fderiv_one_mul`, `integral_fderiv_I_mul`: if `g(1) = 0`, then
  `∫ Dφ_g(z)(1 · z) = -2 ∫ φ_g` and `∫ Dφ_g(z)(i z) = 0`. These are
  `integral_fderiv_apply_self` and `integral_fderiv_apply_I_mul_self`.

## The functional

* `shift ds hn j c : KFs n ds →ₗ[ℂ] KFs n ds` is `g_c(v) = π(1 ⊗ c E_jj) v - κ_j(c) v`.
  `coe_shift`: as a function this is `R(c E_jj) v - κ_j(c) v`. `integrand_eq_shift`:
  `integrand ds hn i j hj c v z = g_c(v)(s x(z))`. `shift_apply_one`: `g_c(v)(1) = 0`
  (`one_diag`). `integrable_shift`: `z ↦ g_c(v)(s x(z))` is integrable.
* `functional LF hD c : KFs n ds →ₗ[ℂ] ℂ` is `Λ_c(v) = ∫ g_c(v)(s x(z)) dz`. It is linear by
  `integral_add` and `integral_const_mul`. `functional_apply`:
  `Λ_c(v) = ∫ integrand ds hn i j hj c v z dz`.
* `functional_strictUpper`: `Λ_c(π(1 ⊗ X) v) = 0` for `X` strictly upper triangular. Proof:
  by `lie_comm`, `g_c(π(1 ⊗ X) v) = π(1 ⊗ X) g_c(v) + π(1 ⊗ [c E_jj, X]) v`. Both `X` and
  `[c E_jj, X]` are strictly upper triangular, so both integrals vanish by
  `integral_rightDerivative_chart`.
* `functional_diag`: `Λ_c(π(1 ⊗ c' E_kk) v) = ∫ R(c' E_kk) g_c(v) (s x(z)) dz`, because
  `c E_jj` and `c' E_kk` commute.
* `functional_diag_other`, `functional_diag_j`, `functional_diag_i`: with `g = g_c(v)`,
  * `Λ_c(π(1 ⊗ c' E_kk) v) = κ_k(c') Λ_c(v)` for `k ∉ {i, j}`;
  * `Λ_c(π(1 ⊗ c' E_jj) v) = κ_i(c') Λ_c(v) + ∫ Dφ_g(z)(c' z)`;
  * `Λ_c(π(1 ⊗ c' E_ii) v) = κ_j(c') Λ_c(v) - ∫ Dφ_g(z)(c' z)`.

  These follow from `diag_other`, `diag_j` and `diag_i`.
* `isComplexJacquetFunctional_functional`: `Λ_c` is a Jacquet functional
  (`IsComplexJacquetFunctional n (complexStandardLie n ds) Λ_c a b`) for any `a`, `b` with
  `a_k = κ_k(1)` and `b_k = κ_k(i)` for `k ∉ {i, j}`, and
  `a_i = κ_j(1) + 2`, `a_j = κ_i(1) - 2`, `b_i = κ_j(i)`, `b_j = κ_i(i)`. Proof: the
  nilpotent condition is `functional_strictUpper`. For the diagonal conditions, insert
  `∫ Dφ_g(z)(1 · z) = -2 Λ_c(v)` and `∫ Dφ_g(z)(i z) = 0` (`g(1) = 0`) into
  `functional_diag_i` and `functional_diag_j`.

## Specialization to an adjacent swap

* `kappa_one`, `kappa_I`: `κ_k(1) = 2 t_k + (n - 1) - 2k` and `κ_k(i) = i l_k`.
* `getElem_append_cons_cons_left`, `getElem_append_cons_cons_right`,
  `getElem_append_cons_cons_of_ne`: the entries of `pre ++ x :: y :: post` at `|pre|` and
  `|pre| + 1` are `x` and `y`. At every other index they do not depend on `x` and `y`.
* `exists_swapJacquetFunctional pre post d e hn hes i j hi hj hre LF hnz`: let
  `ds = pre ++ d :: e :: post` and `es = pre ++ e :: d :: post` (with `hes : es.length = n`),
  `i = |pre|`, `j = i + 1`, `0 ≤ Re(t_d - t_e)`, and `LF : ChartLieFacts ds hn i j hj`. Suppose
  some `c` and some `f ∈ KFs n ds` have `∫ integrand ds hn i j hj c f z dz ≠ 0`. Then there is
  a nonzero `ℓ : KFs n ds →ₗ[ℂ] ℂ` that is a Jacquet functional with exponents
  `a_k = 2 t^{es}_k + (n - 1) - 2k` and `b_k = i l^{es}_k`, read off `es`. Proof:
  `ℓ = Λ_c` with the decay `chartDecay`. It is nonzero by `functional_apply`. The exponents
  match `isComplexJacquetFunctional_functional`: `es` and `ds` agree away from `i, j`,
  `es_i = e = ds_j`, `es_j = d = ds_i`, and
  `2 t_e + (n - 1) - 2i = κ_j(1) + 2`, `2 t_d + (n - 1) - 2j = κ_i(1) - 2` since `j = i + 1`.
