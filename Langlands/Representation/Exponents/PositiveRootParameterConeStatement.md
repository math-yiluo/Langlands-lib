# Weighted scalar-root parameters and strict prefix cones

`Langlands.Exponents.PositiveRootParameterConeStatement` is an internal
proposition definition, with no proof in this module. It compares the
published definitions `RelativeRegularComparison.IsPositiveRootParameter`
and `Exponents.IsPositiveRootCone`.

For every rank `n`, ordered shape `D`, refinement `R`, and real vector `v` on
the actual flattened block indices, it states that `v` is a positive-root
parameter exactly when, in each block `i` of `D`, the vector

`x k = ((R i).size k : ℝ) * v (D.flattenBlockEquiv R ⟨i, k⟩)`

has total sum zero and strictly positive proper initial sums. The proper
initial sums use the existing `Exponents.partialSum`: the sum below each
natural index `a` with `0 < a < (R i).length`. The flattening equivalence,
fine sizes, and strict inequalities are all unchanged.

The provenance is internal finite algebra. Multiplication by each positive
fine size cancels the reciprocal sizes in the scalar roots, leaving the
adjacent vectors `e_j - e_(j+1)`. Their coefficients are the proper initial
sums of `x`; conversely, adjacent differences of those sums recover `x`
when its total is zero. This is the coordinate comparison suggested by
Worker 156, using the published simple-root cone API in `Exponents.Chambers`.
It is not asserted to be a literal statement from an original source.

All ranks, including zero, are quantified. An unrefined block has one fine
block: there are no proper initial sums or adjacent coefficients, and
the total-zero condition forces its parameter to vanish. No character,
Jacquet exponent, analytic inequality, support map, or unitarizability
result is asserted. In particular, this proposition alone does not prove
positive-root cuspidal support.
