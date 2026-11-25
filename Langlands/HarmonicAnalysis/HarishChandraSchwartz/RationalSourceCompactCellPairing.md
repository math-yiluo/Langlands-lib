# Compact integrals on the opposite open cell

`CompactOppositeCellIntegralStatement` gives the compact-open test integral
used in Waldspurger V.1.1 (printed p. 292) with the actual measures of I.1
(printed p. 240). Its first premise is that the ambient group `G` is
connected reductive, as in Waldspurger I.1 (printed p. 238); for other
affine groups of finite type the formula can fail. The function is
strongly measurable, left invariant by the parabolic compact trace, and
supported on the product of the parabolic with the opposite radical's
compact trace. The resulting integral on the opposite compact trace has
the inverse of the original source gamma.

`compactOppositeCellIntegral` proves the proposition. The proof restricts the published ambient Haar identity in the two-factor
open cell. Injectivity of the cell map ensures that the support condition
limits the opposite factor to its compact trace. On that trace the ambient
compact indicator restricts the parabolic factor to its compact trace,
where left invariance removes it from the integrand. The latter trace has
mass one, and inversion preserves the actual opposite radical Haar measure.
