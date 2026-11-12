# Hyperbolic pairs over a division algebra with involution

This internal derived unit constructs a hyperbolic pair for the published
quotient-valued quadratic form, from a nonzero singular vector and an invertible
polar Gram matrix. It works in every characteristic over any division algebra
with an involution of the first kind. A positive quadratic Witt index supplies
the required nonzero singular vector, by attainment of the maximum dimension.

For a nonzero row vector `x`, invertibility of the polar matrix makes the row
`x H` nonzero. A nonzero coordinate and its inverse produce a row `y` with
`h_q(x,y) = 1`. Hermitian symmetry gives `h_q(y,x) = 1`.
Choose a representative `a` of `q(y)` in the alternating quotient. Replace `y`
by `y - a x`. Polarization, singularity of the full line `D x`, and equality of
the quotient classes of `a` and `σ(a)` make this new vector singular. Its pairing
with `x` remains one because `h_q(x,x) = 0`.

The proof uses only the finite-dimensional definitions from `Quaternionic.Forms`,
the identities in `QuadraticFormIdentities`, and elementary matrix linear algebra.
No division by two or characteristic restriction enters the construction.
