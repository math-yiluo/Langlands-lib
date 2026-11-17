# Two-sided bounds on rectangular diagonal corrections

This internal module defines `IsNormBoundedUnitTuple c C`: every value
of the unit tuple `c`, and every inverse value, has norm at most `C`.
It is a concrete pointwise bound, without an existence or integration
premise.

For a factorization of the lower unipotent
`lowerBlockPair 1 x 1 = U*diag(c)*K`, suppose the entries of `x` are
bounded by `C ≥ 1`, `U` is upper unitriangular, and the entries of
`K` and `K⁻¹` have norm at most one. Then the tuple `c` has the
two-sided bound `(a+d)*C`. For an ultrametric norm the bound is `C`.

The implemented proof applies the entry bounds from
`RectangularDiagonalCorrection` to the triangular factor and its
inverse. Its diagonal equals `c`. The published `diagonalUnit`
packages that diagonal with the corresponding inverse diagonal, so
equality of units identifies the inverse values as well. The proof
does not require a determinant estimate.

As a consequence, any ratio `c_i/c_j` has norm at most `C²` whenever
the tuple has the two-sided bound `C`. This applies in either order
of the indices, so it controls the inverse correction roots needed
to recover original leading roots.

All factorization hypotheses remain explicit. This module does not
assert an adelic common denominator, rapid decay, or convergence.
