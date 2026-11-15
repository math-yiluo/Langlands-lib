# A test vector for the rank-one Jacquet integral

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetNonvanishing`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`.

## Main result

`exists_integral_integrand_ne_zero`: let `ds = pre ++ d :: e :: post` with
`hn : ds.length = n`, `hi : (i : ℕ) = pre.length` and `hj : (j : ℕ) = i + 1`, so that `d` and
`e` sit at the positions `i` and `j`. Assume `0 ≤ Re(t_d - t_e)`, where `t` is the exponent.
The statement also takes `(l_d, t_d) ≠ (l_e, t_e)`, but the proof does not use it. Then there
are `c ∈ ℂ` and `f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` with

`∫_ℂ integrand ds hn i j hj c f z dz ≠ 0`,

where `integrand ds hn i j hj c f z = R(c E_jj) f (C(z)) - κ_j(c) f(C(z))`
(`ComplexSwapJacquetChart`). The integral is the Bochner integral for Lebesgue measure on `ℂ`.
`ComplexSwapJacquetFunctional` (Worker 48) shows that `f ↦ ∫ integrand c f` is a Jacquet
functional with the swapped exponents. This theorem makes it nonzero.

## The test vector

`F(g) = N(g s)`, where `N = nzFunction n ds` is the `U(n)`-finite vector of the Library's
`ComplexStandardNontrivialProof` and `s` is the permutation matrix of `(i j)`.

* `nzFunction_mem_kFiniteFunctions`: `g ↦ N(g)` lies in the `U(n)`-finite functions of the
  standard module. Smoothness and the transformation law repeat the argument inside the
  Library's proof of `complexStandardNontrivial`, which does not export it as a lemma. It uses
  the public lemmas `contDiffOn_nzFunction`, `nzFunction_mul_of_isUpperTriangular`,
  `principalSeriesCharacter_eq` and `nzFunction_mem`.
* `swap_mem_unitaryCompact` and the Library's
  `rightTranslation_mem_kFiniteFunctions_complexStandardModule`: `F` is again `U(n)`-finite.
* `swap_mul_transvection_mul_swap`: `F(C(z)) = N(s x(z) s) = N(1 + z E_{ji})`.
* `lowMinor_transvection`: every bottom-right minor of `1 + z E_{ji}` is `1`. The matrix is the
  transpose of the upper unitriangular `1 + z E_{ij}` (`transvection_isUpperTriangular`,
  `transvection_apply_self`, `transvection_eq_transpose`), so the Library's
  `det_lowBlock_of_isUpperTriangular` applies.
* `lowGram_eq_normSq_lowMinor`: if the rows `≥ k` of `Y` vanish in the columns `< k`, the Gram
  determinant of these rows is `|det(bottom-right block)|²`. The rows equal the block times the
  row selector, and the Library's `lowSelector_mul_conjTranspose` gives `P Pᴴ = 1`. This gives
  `lowGram_transvection_of_ne`: for `k ≠ j` the Gram determinants of `1 + z E_{ji}` are `1`.
* `lowGram_transvection_self`: for the rows `≥ j`, `R Rᴴ` is the corresponding block of
  `Y Yᴴ = 1 + E_{ji}(z) + E_{ij}(z̄) + E_{jj}(|z|²)`, namely `diag(1 + |z|², 1, …, 1)`. Its
  determinant is `1 + |z|²`.
* `nzFunction_transvection`: hence `F(C(z)) = exp(σ log(1 + |z|²)) = (1 + |z|²)^σ`, with
  `σ = w_j - |μ_j|/2`, where `w_j` and `μ_j` are the minor exponent and minor weight
  (`nzExponent`, `nzWeight`) at `j`. In the main proof, `posWeight_append_cons(_succ)` and
  `posExponent_append_cons(_succ)` give `σ = -1 - (t_d - t_e) - |l_e - l_d|/2`.

## The integrand

By `rightDerivative_chart_diag_j` (`ComplexSwapJacquetLie`), the integrand equals
`(κ_i(c) - κ_j(c)) φ(z) + Dφ(z)(c z)` with `φ(z) = (1 + |z|²)^σ`. By
`fderiv_exp_log_one_add_norm_sq_apply` (chain rule with `D(|z|²)(v) = 2 ⟨z, v⟩`),
`Dφ(z)(c z) = 2|z|² Re c · σ φ(z) / (1 + |z|²)`.

* `l_d = l_e`: take `c = 1`. Then `κ_i(1) - κ_j(1) = 2 (t_d - t_e) + 2` and `σ = -1 - (t_d - t_e)`.
  The integrand simplifies pointwise to `(2 (t_d - t_e) + 2) (1 + |z|²)^(σ - 1)`. Its integral is
  `(2 (t_d - t_e) + 2) π / (1 + t_d - t_e)`, nonzero since both real parts are `≥ 1`.
* `l_d ≠ l_e`: take `c = i`. Then `Re c = 0`, the derivative term vanishes, and
  `κ_i(i) - κ_j(i) = i (l_d - l_e)`. Since `|l_e - l_d| ≥ 1`, `Re σ < -1`, and the integral is
  `i (l_d - l_e) π / (-(σ + 1))`, nonzero because `Re(-(σ + 1)) > 0`.

## The radial integral

`integral_one_add_norm_sq_cpow`: `∫_ℂ exp(β log(1 + |z|²)) dz = π / (-(β + 1))` for
`Re β < -1`.

* Integrability on `ℂ`: the modulus is `(1 + |z|²)^{Re β}`, dominated by Mathlib's
  `integrable_rpow_neg_one_add_norm_sq`.
* Mathlib's `integral_fun_norm_addHaar` (polar coordinates, `volume(ball 0 1) = π` by
  `Complex.volume_ball`) gives `2π ∫_0^∞ r (1 + r²)^β dr`. The one-dimensional integrability
  follows from `integrable_fun_norm_addHaar`.
* `(1 + r²)^{β+1} / (2(β + 1))` is a primitive of `r (1 + r²)^β` and tends to `0` at `∞`, since
  `Re(β + 1) < 0`. So `integral_Ioi_of_hasDerivAt_of_tendsto'` gives `-1/(2(β + 1))`, hence
  `2π · (-1/(2(β+1))) = π/(-(β+1))`.

## Provenance

This is an internal step of the proof of `ComplexStandardPermutationStatement`: the nonvanishing
of the rank-one intertwining functional. The choice of `F` and the elementary computations above
are our own. The interface (`exists_integral_integrand_ne_zero` with this exact type) was agreed
with Worker 48, whose `ComplexSwapJacquetProof` consumes it.
