# Zero padding of Jacobi–Trudi weights

Author: Worker 1767.

This internal helper appends zero coordinates to an integral weight. The
Jacobi–Trudi determinant in a supplied finite alphabet has zero lower-left
block after this padding, while its lower-right block is the zero-weight
upper-triangular matrix with diagonal one. Reindexing by the finite sum
coordinates and applying the block determinant identity therefore leaves the
original determinant unchanged.

The argument permits arbitrary integral input weights and independent alphabet
and matrix sizes. In particular, the same-rank Jacobi–Trudi polynomial of a
zero-padded weight in a larger alphabet equals the smaller Jacobi–Trudi matrix
in that larger alphabet. This supplies the algebraic rank comparison needed
between the Cauchy sum and the unequal-rank Whittaker formula.
