# Consequences of grading data: weights, dual bases and the Cartan part of brackets

Module `Langlands.Algebra.ParabolicCenterProjectionGrading`, namespace
`Langlands.Algebra.ParabolicCenterProjection.GradingData`.

Fix grading data `D : GradingData g H` (module `Langlands.Algebra.ReductiveGradingData`).

## Gradings and weights

- `φ i = Re (wt i reg)` and `ev i = wt i reg`; `re_ev` and `lie_reg` say that `φ = Re ∘ ev` and
  `⁅reg, b i⁆ = ev i • b i`, the data used by `Langlands.Algebra.LieWeightCenterProjection`.
- `φ_eq_zero_iff`: `φ i = 0` exactly when `wt i = 0`; then `b i ∈ cartan`
  (`mem_cartan_of_φ_eq_zero`).
- `φ_eq_zero_of_repr_ne_zero`, `mem_cartan_of_commute`, `center_le_cartan`: a vector commuting
  with `cartan` has coordinates only on basis vectors of grading zero, hence lies in `cartan`; in
  particular the centre lies in `cartan`.
- `wt_eq_neg_of_form_ne_zero`, `φ_eq_neg_of_form_ne_zero`, `φ_eq_add_of_repr_lie_ne_zero`,
  `form_eq_zero_of_commute`: the form pairs only opposite weights; brackets add weights; vectors
  commuting with `cartan` are orthogonal to the basis vectors of nonzero grading.
- `eq_of_form_basis`, `form_basis_separating`: a vector is determined by its pairings with the
  basis.

## The dual basis and the vectors `T γ`

- `dual` is the dual basis of `basis` for the form (`form_dual`). `lie_dual`: `b^i` has weight
  `-wt i`.
- `dualOf γ = ∑_{φ c = 0} γ (b c) • b^c` for a linear form `γ` on `cartan`. It lies in `cartan`
  (`dualOf_mem_cartan`), has coordinates only on letters of grading zero
  (`repr_dualOf_eq_zero`), represents `γ`: `B (T γ) h = γ h` for `h ∈ cartan`
  (`form_dualOf`, `form_dualOf_cartan`, using `cartan_eq_sum`), and `T (wt i) ≠ 0` for
  `wt i ≠ 0` (`dualOf_wt_ne_zero`).
- `repr_lie_of_φ_eq_zero`: the grading-zero coordinates of `⁅b e, b i⁆` are those of
  `-B (b e, b i) T (wt i)`. If `wt e = -wt i`, the vector
  `⁅b e, b i⁆ + B (b e, b i) T (wt i)` pairs to zero with every basis vector (invariance for the
  grading-zero ones, orthogonality of weight-zero vectors for the others), hence vanishes;
  otherwise both sides vanish.
- `exists_shiftPart_ne_zero_g`: the nondegeneracy hypothesis of
  `LieCenterProjectionInjective.center_eq_zero_of_mem_positiveWeightRightIdeal` for `g`, from
  `LieCenterProjectionInjective.exists_shiftPart_ne_zero` with `T = dualOf`.

## The Cartan subspace

`cartan_le_span_dualOf_sup_center`: `cartan` lies in the span of the vectors `T (wt q)` plus the
centre. The restriction of the form to `cartan` is nondegenerate. If the span were proper, a
nonzero linear form on `cartan` would vanish on it; represent it as `B (h₀, ·)` (Mathlib's
`LinearMap.BilinForm.toDual`). Then `wt q h₀ = B (T (wt q), h₀) = 0` for all `q`, so `h₀` is
central, and `B (h₀, c) = 0` for all central `c` forces `h₀ = 0`.

## Provenance

Internal. The vectors `T γ` are the elements of the Cartan subalgebra dual to linear forms
through the invariant form, as `t_α` for roots `α` in the classical theory.
