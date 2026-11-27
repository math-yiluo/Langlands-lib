# Cartan and grading data for a reductive Lie algebra with an integral grading element

Module `Langlands.Algebra.ReductiveGradingData`, namespace
`Langlands.Algebra.ParabolicCenterProjection`.

## The structure

`GradingData g H`, for a complex Lie algebra `g` and `H : g`, bundles:

- `cartan : Submodule ℂ g` containing `H` (`H_mem`), with `⁅x, y⁆ = 0` on it (`lie_eq_zero`);
- a finite index type `ι`, a basis `basis : Basis ι ℂ g` and linear weights
  `wt i : cartan →ₗ[ℂ] ℂ` with `⁅h, basis i⁆ = wt i h • basis i` (`lie_basis`), and
  `basis i ∈ cartan` when `wt i = 0` (`mem_of_wt_eq_zero`);
- a bilinear form `form`, nondegenerate, symmetric and invariant, and nondegenerate on the
  centre of `g` (`center_nondegenerate`);
- an element `reg ∈ cartan` with `Re (wt i reg) = 0` exactly when `wt i = 0`
  (`re_wt_reg_eq_zero_iff`), and `Re (wt i reg) > 0` whenever `wt i H` is a positive integer
  (`re_wt_reg_pos`).

## Existence

`nonempty_gradingData`: a finite-dimensional complex Lie algebra with `radical = center`, with an
element `H` whose integral eigenvectors span it, has grading data. This combines
`ReductiveCartanData.exists_cartanData` with `exists_regular` of
`Langlands.Algebra.ParabolicCenterProjectionWeights`.

## Provenance

Internal packaging of the structure theory used in the proof of
`ParabolicCenterProjectionFiniteStatement`.
