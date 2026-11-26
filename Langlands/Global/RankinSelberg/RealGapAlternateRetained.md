# Logarithmic coordinates and endpoint estimates in the real alternate gap chart

This module is the real counterpart of the Library's `ComplexGapAlternateRetained`; the statement is the
same, with the real Iwasawa coordinate `RealIwasawa.alpha`, the real height `H = realMatrixHeight`, the
orthogonal group and the real torus `RealIwasawa.torus`.

The retained matrix of `RealGapTriangularChart` is `u · diag(1, torus y) · packedTail (firstRectangle x) 1`
with `u` orthogonal. `firstRetainedColumn p` is its first tail column and `lastRetainedInverseRow p` the
last row of its inverse.

`RealGapAlternateRetainedStatement` (proved by `realGapAlternateRetained`): for `g ∈ GL_k(ℝ)` and outer
coordinates `p = (((g₁, y), u), x)`,

1. `alpha (diag(g, 1) · retainedMatrix(p)^{-1}) = Fin.append (alpha g) (-y)`
   (`alpha_rankInclusion_mul_retained_inv`);
2. `H(retainedMatrix p) ≤ (1 + 2n²)(2n²) · exp(2 ∑_j |y_j|) · (1 + ‖x‖)²` with `n = k + q + 1`
   (`height_retained_le`);
3. `‖x‖ ≤ n ‖firstRetainedColumn p‖`, `exp(y_0) ≤ n ‖firstRetainedColumn p‖` and
   `exp(-y_q) ≤ n ‖lastRetainedInverseRow p‖` (`retained_endpoint_norms`).

For (1), conjugating the inverse of the unipotent factor by `diag(g, 1)` keeps it upper unipotent, and
the Iwasawa coordinate of `diag(g, torus(-y)) · u^{-1}` is computed blockwise from the Iwasawa
decomposition of `g` (`npart_mul_torus_mul_kpart`, `alpha_iwasawa`, `alpha_unipotent_mul`); the block
sum of orthogonal matrices is orthogonal. For (2), the height is submultiplicative
(`realMatrixHeight_mul_le`), the torus–orthogonal factor is bounded by
`RealWhittakerGauge.realMatrixHeight_torus_mul_le` (weakened to the constant `1 + 2n²`), and the entries
of the unipotent factor and its inverse are at most `1 + ‖x‖`. For (3), removing the orthogonal factor,
whose entries are at most one in absolute value, exposes the rectangle and the first diagonal entry in
the first tail column and the inverse of the last diagonal entry in the last inverse row.

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
