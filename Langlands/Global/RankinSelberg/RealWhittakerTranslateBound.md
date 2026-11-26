# Polynomial dependence on real Whittaker right translations

Write `H = realMatrixHeight` for Jacquet's height `Σ_{i,j} (|g_{ij}|² + |(g⁻¹)_{ij}|²)`.

* `exists_abs_alpha_unitary_mul_le`: there is `K ≥ 1` with
  `|alpha (k b) i| ≤ log (K · H(b))` for all orthogonal `k`, all `b` and all `i`. The diagonal of
  the triangular Iwasawa factor of `k b` and of its inverse are entries of these matrices
  (`exp_alpha` and the private `inverse_diagonal`), so they are bounded by the height, which is
  submultiplicative (`realMatrixHeight_mul_le`) and bounded on the compact orthogonal group.
* `exists_rightTranslate_loss`: if `‖W g‖ ≤ C exp(N Σ|alpha g| - J rootPos(alpha g))` for all `g`,
  then `‖W(g b)‖ ≤ C (K H(b))^{N(r+1) + 2Jr} exp(N Σ|alpha g| - J rootPos(alpha g))`, by
  `alpha_right_mul` and the bound on the displacement.
* `RealWhittakerTranslateBoundStatement` and `realWhittakerTranslateBound`: every `W` with a
  gauge bound (`HasGaugeBound`) has a growth order `N` such that for every `J` there is `C ≥ 0`
  with `‖W(g b)‖ ≤ C H(b)^{N(r+1) + 2Jr} exp(N Σ|alpha g| - J rootPos(alpha g))` for all `g`, `b`.
* `translateBound_of_mem_model`: this applies to every member of `realUniformWhittakerModel`.

This is the real counterpart of the Library's `ComplexWhittakerTranslateBound`, used for the
majorants of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg Integrals*
(2009), §10.2–§10.3.
