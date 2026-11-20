# Exponent deformation for complex standard modules

In the normalized complex principal series, moving the exponent of one
character by `z` leaves its angular weight unchanged. This module constructs
the resulting identification on the `U(n)`-finite spaces and computes the Lie
action on the original space as a function of `z`.

Write `G_p(g)` for the positive determinant of the Gram matrix of the rows at
positions `p` and higher. The definition `diagonalLog` takes
`log G_p(g) − log G_(p+1)(g)`. Under left multiplication by `diag(a) u`, the
change in this difference is `log |a_p|²`. Under right multiplication by a
unitary matrix the difference stays fixed, and it vanishes on `U(n)`. These
identities follow from the tail Gram determinant formulas of
`ComplexDuality.GramWeight`.

Multiplication by `exp(z · diagonalLog p)` changes the normalized Borel
character by `|a_p|^(2z)`. Multiplication by its reciprocal gives the inverse.
Both multipliers preserve compact finiteness by equivariance for right
translation by `U(n)`. When the list has length `n`, `shiftEquiv` identifies
the compact actions on the two standard modules. Each function and its image
under `shiftEquiv` have the same restriction to `U(n)`.

To compute the transported Lie action, differentiate the scalar multiplier and
the old function by the product rule, then multiply by the reciprocal. The
result is the original right derivative plus `z` times multiplication by the
right derivative of `diagonalLog`. The theorem `transportedDerivative_affine`
expresses this on the original standard module. It obtains the linear
coefficient by subtracting the old action from the transported action at `1`.

This is an internal calculation for transferring constituents under adjacent
swaps. Badulescu and Renard (2010), Definition 2.2 and Remark 2.3 on p. 1123
(PDF p. 10), and Proposition 2.4 on p. 1124 (PDF p. 11), give the normalized
induction convention and the reordered-product constituent comparison that
motivates the application. The Gram determinant construction and the affine
formula are derived here.
