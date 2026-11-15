# Right derivatives along the rank-one chart

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetLie`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`.

This module supplies the pointwise Lie-algebra identities used by the rank-one Jacquet functional
of `ComplexSwapJacquetFunctional`. Fix a list `ds` of complex characters with
`hn : ds.length = n`, adjacent positions `i` and `j` with `hj : (j : ℕ) = i + 1`, and
`f ∈ complexStandardModule n ds`, the smooth principal series of `GL_n(ℂ)`. Write `R(X)` for
`rightDerivative (matrixModel ℂ n) X`, and `C(z) = chart i j hj z = s x(z)`. Here `s` is the
permutation matrix of the transposition `(i j)` and `x(z) = 1 + z E_{ij}`
(`ComplexSwapJacquetChart`). Also write `φ(z) = f(C(z))` and
`κ_k(c) = kappa ds hn k c = Re c · (2 t_k + (n - 1) - 2k) + Im c · i l_k`, where `t_k` and `l_k`
are the exponent and weight of the `k`-th character.

## Results

All are stated exactly as follows. `E_{ab}(w)` is `Matrix.single a b w`, "strictly upper" means
`∀ a b, b ≤ a → X a b = 0`, and each statement holds for every `z ∈ ℂ`.

* `contDiff_chartRestrict` (P1): if `f` is smooth (`ContMDiff`), then `φ` is `C^∞` on `ℂ` as a
  real vector space.
* `rightDerivative_chart_single_ij` (P3): if `f` is smooth, then
  `R(E_{ij}(w)) f (C(z)) = Dφ(z)(w)` (real Fréchet derivative).
* `rightDerivative_chart_strictUpper` (P2): `R(X) f (C(z)) = 0` for `X` strictly upper with
  `X_{ij} = 0`.
* `rightDerivative_chart_diag_other` (P4): `R(E_{kk}(c)) f (C(z)) = κ_k(c) f(C(z))` for
  `k ≠ i, j`.
* `rightDerivative_chart_diag_j` (P5): `R(E_{jj}(c)) f (C(z)) = κ_i(c) f(C(z)) + Dφ(z)(c z)`.
* `rightDerivative_chart_diag_i` (P6): `R(E_{ii}(c)) f (C(z)) = κ_j(c) f(C(z)) - Dφ(z)(c z)`.
* `rightDerivative_one_strictUpper` (P7a): `R(X) f (1) = 0` for `X` strictly upper.
* `rightDerivative_one_diag` (P7b): `R(E_{kk}(c)) f (1) = κ_k(c) f(1)`.

## Proof

Everything is computed in matrix coordinates. By the Library theorem `rightDerivative_eq_fderiv`
(`PrincipalSeriesStability`), `R(X) f (g) = Df̃(g)(g X)`, where `f̃ = unitsExtension f` is the
extension of `f` by zero to all matrices.

**Equivariance of `f̃`.**

* `unitsExtension_unipotent_mul_eq`: `f̃(u g) = f̃(g)` for upper unipotent `u`. It follows from
  the Library's `ComplexDuality.LieInvariance.unitsExtension_unipotent_mul` and
  `principalSeriesCharacter_one` (the character is `1` at `1`, via `principalSeriesCharacter_eq`
  and `unitChar_one`). With the Library theorem
  `ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero`, this gives `Df̃(y)(N y) = 0` for
  strictly upper `N`.
* `fderiv_unitsExtension_single_mul`: `Df̃(g)(E_{kk}(c) g) = κ_k(c) f(g)`. The curve
  `γ(t) = g + (e^{tc} - 1) E_{kk} g` equals `diag(1, …, e^{tc}, …, 1) g` and has derivative
  `E_{kk}(c) g` at `0`. Along it `f̃` is `χδ^{1/2}(diag(…)) f(g)`
  (`ComplexDuality.LieInvariance.unitsExtension_diagonal_mul`). By `principalSeriesCharacter_eq`
  this character is `unitChar μ_k W_k (e^{tc})`, with `μ_k = l_k` and
  `W_k = t_k + (n - 1)/2 - k`. `unitChar_exp` evaluates it as `exp(t (μ_k i Im c + 2 W_k Re c))`.
  Its derivative at `0` is `κ_k(c)` (`kappa_eq`, using `posWeight_eq_get` and
  `posExponent_eq_get` to identify the position data with the list entries).

**Matrix algebra of the chart.** `s E_{ab}(x) = E_{σa, b}(x)` and `E_{ab}(x) s = E_{a, σb}(x)`
for `σ = (i j)` (`swap_mul_single`, `single_mul_swap`), and `(s M s)_{ab} = M_{σa, σb}`
(`swap_mul_mul_swap_apply`). Products of `x(z)` with `E_{ab}` are expanded by
`transvection_mul_single_self` / `_of_ne` and `single_mul_transvection_self` / `_of_ne`. From
these:

* `chart_mul_single_ij`, `chart_mul_single_ij'`: `C(z) E_{ij}(w) = s E_{ij}(w) = E_{jj}(w)`;
* `chart_mul_single_jj`: `C(z) E_{jj}(c) = E_{ii}(c) C(z) + C(z) E_{ij}(c z)`;
* `chart_mul_single_ii`: `C(z) E_{ii}(c) = E_{jj}(c) C(z) - C(z) E_{ij}(c z)`;
* `chart_mul_single_kk`: `E_{kk}` commutes with `C(z)` for `k ≠ i, j`;
* `transvection_conj_apply_eq_zero`, `swap_le_or`: for `X` strictly upper with `X_{ij} = 0`, the
  matrix `M = x(z) X x(-z)` vanishes on and below the diagonal and at `(i, j)`. Since
  `σ = (i j)` preserves the order of every pair except `(i, j)`,
  `N = s M s = C(z) X C(z)⁻¹` is strictly upper.

**The results.**

* P1 and P3: `φ = f̃ ∘ (z ↦ s x(z))` (`chartRestrict_eq_comp`). The map `z ↦ s x(z)` is affine
  with linear part `w ↦ s E_{ij}(w)` (`singleCLM`, `hasFDerivAt_chartMatrix`,
  `contDiff_chartMatrix`), so P1 follows from the Library's `contDiffOn_unitsExtension`. For P3
  the chain rule gives `Dφ(z)(w) = Df̃(C(z))(s E_{ij}(w))`, and `s E_{ij}(w) = C(z) E_{ij}(w)`.
* P2: `C(z) X = N C(z)` with `N` strictly upper (above); apply
  `fderiv_strictUpper_mul_eq_zero`.
* P4–P6: rewrite `C(z) E_{kk}(c)` by the chart identities, then use linearity of `Df̃(C(z))`,
  `fderiv_unitsExtension_single_mul` and P3.
* P7a, P7b: the same statements at `g = 1`.

## Relation to other Library results

* `unitChar_exp` evaluates `unitChar` at `e^x` for complex `x`. The derivative along
  `c E_kk` with non-real `c` needs this. `ComplexJacquetBorel.borelFactor_exp` treats only real
  `x` (and `borelFactor_eq_unitChar` relates the two functions).
* `posWeight_eq_get` and `posExponent_eq_get` read the position data of an arbitrary list. The
  Library's `posWeight_ofFn` and `posExponent_ofFn` (`ComplexJacquetBorel`) are the special
  case `List.ofFn d`, and the lists here are not given in that form.
* `ComplexDuality.LieInvariance.fderiv_diagonal_mul_eq` computes the diagonal derivative of a
  function that transforms under the diagonal torus by the modulus character `δ` (a product
  `f h` with `h` in the inverse principal series); only the real parts of the direction enter.
  `fderiv_unitsExtension_single_mul` is the analogous computation for an arbitrary
  principal-series character and a complex direction `c E_kk`.

## Provenance

These are internal lemmas for the rank-one Jacquet functional in the proof of
`ComplexStandardPermutationStatement`. The identities are elementary matrix calculus. Their exact
form (P1–P7) is the interface agreed with Worker 48's `ComplexSwapJacquetFunctional`, which
packages them as `ChartLieFacts`.
