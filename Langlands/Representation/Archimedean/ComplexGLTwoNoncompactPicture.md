# The noncompact picture of the `GL_2(ℂ)` principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoNoncompactPicture`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`). The
formulas are the standard action of `𝔤𝔩_2(ℂ)` on the principal series in the noncompact
picture, derived here from the Library's chart formulas.

## Setting

`d 0`, `d 1` are complex characters with exponents `t_0`, `t_1` and weights `l_0`, `l_1`. The
standard module of `List.ofFn d` consists of the functions `f` on `GL_2(ℂ)` with the
principal-series transformation law of the Library.

* `wn z = C(z)` is the Library chart `ComplexSwapJacquet.chart 0 1 z`; its matrix is
  `[[0, 1], [1, z]]` (`wn_val`), and `complexGLTwoWeyl * complexGLTwoUnipotent z = wn z`
  (`weyl_mul_unipotent`), so `C(z) = w n(z)` with the Weyl and unipotent elements of
  `ComplexGLTwoJacquetOrderingReduction`.
* `ncp f z = f(C(z))` is the noncompact picture `φ_f` of `f`.
* `pp d = p = t_0 - t_1 + (l_0 - l_1)/2` and `qq d = q = t_0 - t_1 - (l_0 - l_1)/2`.
* `kappa_ofFn`: the Library character derivative `κ_k(c)` (`ComplexSwapJacquet.kappa`) equals
  `((a_k + l_k)/2) c + ((a_k - l_k)/2) c̄` with `a_k = 2 t_k + 1 - 2k`. Proof: substitute
  `Re c = (c + c̄)/2` and `Im c = (c - c̄)/(2i)` in its definition.

## Right derivatives

For `f` in the standard module, `φ = ncp f`, and `∂φ`, `∂̄φ` its Wirtinger derivatives
(`ComplexGLTwoWirtinger`); `fderiv_ncp_apply` writes `Dφ(z)(w) = ∂φ(z) w + ∂̄φ(z) w̄`.

* `ncp_single01`: `φ_{R(c E_01) f} = c ∂φ + c̄ ∂̄φ`, from the Library's
  `rightDerivative_chart_single_ij` (`R(c E_01) f (C(z)) = Dφ(z)(c)`).
* `ncp_single00`: `φ_{R(c E_00) f}(z) = κ_1(c) φ(z) - Dφ(z)(c z)`, and `ncp_single11`:
  `φ_{R(c E_11) f}(z) = κ_0(c) φ(z) + Dφ(z)(c z)`, from the Library's `ChartLieFacts`
  (`diag_i`, `diag_j`) for the chart `C`.
* `wn_mul_single_one_zero` (direct matrix computation):
  `C(z) (c E_10) = (c E_01) C(z) - (c z E_00) C(z) + (c z E_11) C(z) + C(z) (-c z² E_01)`.
* `rightDerivative_wn_single10`: hence
  `R(c E_10) f (C(z)) = (κ_0(-c z) + κ_1(c z)) f(C(z)) + Dφ(z)(-c z²)`. The right derivative is
  the derivative of the extension of `f` to all matrices (`rightDerivative_eq_fderiv`), which is
  linear in the direction; the term `(c E_01) C(z)` contributes `0` because `f` is invariant
  under the upper unipotent group on the left (Library
  `fderiv_strictUpper_mul_eq_zero`), the diagonal terms contribute `κ_0`, `κ_1`
  (`fderiv_unitsExtension_single_mul`), and the last term is `R(-c z² E_01) f (C(z))`.
* `ncp_single10`: substituting `kappa_ofFn`,
  `φ_{R(c E_10) f} = -c (z² ∂φ + (p + 1) z φ) - c̄ (z̄² ∂̄φ + (q + 1) z̄ φ)`.

`hj01` and `single01_strictUpper` are bookkeeping lemmas (`1 = 0 + 1` in `Fin 2`, and
`c E_01` is strictly upper triangular).
