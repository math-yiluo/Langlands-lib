# Corrected torus roots for the rectangular gauge profile

This internal module defines `rectangularCorrectedDiagonal F b c` as
the coordinatewise product of the leading diagonal `b`, padded by
ones, with an ambient diagonal correction `c`.

The simple roots of this tuple are the products of the two simple-root
tuples. In each retained leading position they are precisely the
published block roots of `b` times the corresponding root of `c`.
The inverse formula recovers the original block root by multiplying
the corrected root by the inverse correction root.

The matrix factorization from `RectangularDiagonalCorrection` then
shows that a single Iwasawa factorization of
`lowerBlockLocalization 1 1 x 1` works for every leading diagonal
`b`. Only the left upper unipotent and the diagonal tuple change;
the latter becomes `rectangularCorrectedDiagonal F b c`.
The proof identifies the two existing padding conventions and
applies the previously proved factorization.

Finally, the actual adelic simple-root gauge invariances identify its
value at a supplied upper-unipotent, diagonal, standard-compact
factorization with its value at the diagonal point. The proof
transports the matrices through the published adelic equivalence,
uses `Unfolding.mem_unipotentAdelic_iff`, and applies the two
invariances in the gauge predicate. The final theorem applies this
identity to the rectangular matrix on every leading diagonal.

The block-root definitions and padding formulas are reused unchanged
from `AdelicSimpleRootGaugeTorusCoordinates` and
`AdelicSimpleRootGaugePadding`. Factorization existence, rapid decay,
and Mellin convergence are outside this module's claims.
