# Simple-root restrictions on repeated type C weights

Author: Worker 244 for Task 6244.

This internal combinatorial module defines `Langlands.TypeCBlockWeights.weight`.
Its argument `i` is a zero-based coordinate of the natural symplectic
representation. Coordinates in the `k`-th block, from `k * degree` through
`(k + 1) * degree - 1`, have the `k`-th standard weight in `Fin r → ℤ`.
Coordinates after the first `r` blocks have weight zero.

`simpleRestriction` takes the difference of consecutive weights for every
simple root except the last, where it takes twice the last weight.
For positive `degree` and `r * degree ≤ n`,
`simpleRestriction_ne_zero_iff` says that a simple restriction is nonzero
exactly when its one-based coordinate equals `j * degree` with
`1 ≤ j ≤ r`.

The proof compares membership in consecutive integer intervals. A difference
of consecutive weights is nonzero exactly at a block boundary. For the long
root, multiplication by two is injective in the integer weight lattice, and
the final coordinate has nonzero weight exactly when `r * degree = n`.
This argument also covers `r = 0` and a nonempty weight-zero tail.

Provenance: internal. These are elementary calculations on functions with
integer values, intended to implement the repeated-weight calculation
described in the published `TypeCDistinguishedVerticesStatement.md`. The
module does not identify these weights with any actual group or torus; that
comparison remains a separate proof obligation.
