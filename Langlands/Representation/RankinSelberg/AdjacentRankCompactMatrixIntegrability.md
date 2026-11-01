# Compact matrix convergence after determinant-density cancellation

The derived theorem `AdjacentCompactMatrix.integrable_natWeight_of_compact_bound`
starts with a continuous complex function `f` on `GL_(r+1)(F)`. It assumes a
compact set `K` of square matrices, vanishing of `f` whenever the underlying
matrix lies outside `K`, and a nonnegative uniform bound `C` for `‖f‖` over `K`.
It proves genuine integrability of `|det(g)|^(r+1) f(g)` against the actual
`generalLinearHaar F.Carrier r`. The determinant weight in Lean is the
published complex `determinantWeight` at the natural exponent `r+1`.
All field topologies and normalizations are canonical, the supplied additive
Haar measure `ν` is retained, and `r=0` is included.

The noncomputable definition `matrixZeroExtension F r f` is the extension by
zero of any complex GL function along the underlying-matrix inclusion.
`matrixZeroExtension_apply` gives its value on invertible matrices;
`matrixZeroExtension_of_not_mem_range` gives zero elsewhere.
`measurable_matrixZeroExtension` proves measurability when `f` is measurable.
These definitions and lemmas are used in the integrability proof.

The proof uses the measurable embedding of GL into square matrices to extend
`f` by zero off the invertible locus, via `Function.extend`. The extension is
measurable, bounded everywhere by `C`, and zero outside `K`. The rectangular
additive Haar measure of `K` is finite. `IntegrableOn.of_bound` and extension
from the compact support therefore give additive integrability of this
measurable extension, hence also integrability after restriction to the
invertible locus. The published
`GLDeterminantDensity.integrable_generalLinearHaar_natWeight_iff` transfers
this conclusion to the required GL Haar integrability with the natural
matrix-size determinant weight.

This is internal measure-theoretic infrastructure derived from the imported
measurable-embedding, compact-measure, and determinant-density results. It
does not assume that the zero extension is continuous at singular matrices.
It supplies the measure-transfer step; coefficient growth, the remaining
large-twist exponent bound, and the final adjacent-rank image theorem are
separate obligations.
