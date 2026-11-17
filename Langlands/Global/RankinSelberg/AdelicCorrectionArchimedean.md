# Archimedean bounds for actual diagonal corrections

This internal module defines `diagonalIdeleRow`, which regards an idelic
diagonal tuple as an additive adelic row, and
`archimedeanAdeleProjection`, the ring projection to the published
mixed archimedean space.

For a supplied standard-compact Iwasawa factorization of the lower
rectangular unipotent, both the archimedean diagonal tuple and its
inverse have norm at most
`(a+d+1)*(1+‖rectangleArchimedeanCoordinates x‖)`.
Rectangle matrix norms are the elementwise supremum norms.

The proof first maps the factorization to an arbitrary normed field
and applies the two-sided local correction bound. Extending the
rectangle by one zero row preserves its entry bound. At each real or
complex coordinate, the actual standard compact subgroup and its
inverse give norm bounds by one on the compact factor's entries.
Every projected rectangular entry is bounded by the mixed-space
matrix supremum norm. Applying the local result with
`C=1+‖rectangleArchimedeanCoordinates x‖` and taking finite suprema
gives both asserted row bounds.

The conclusion is linear growth of the correction and its inverse.
It does not yet assert a bound for the full idelic absolute value,
joint Schwartz rapid decay, or Mellin convergence.
