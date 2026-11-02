# Lattice boxes for the actual dominant rectangles

This internal derived module converts compact support of the transformed JPSS
rectangles into standard lattice boxes. It uses the actual matrix conventions
of JPSS (1983), Section 4.10(2), printed page 419; the auxiliary estimates are
proved from the Library's compact support and valuation results.

Membership in a standard box is equivalent to bounding every normalized
absolute value by the corresponding power of the residue cardinality.
Continuity and compactness give a common box for a compact set of matrices.
Entrywise integrality of finite sums and products adds denominator exponents
under rectangular matrix multiplication. A bound on an invertible matrix and
its inverse therefore removes a right factor with that exponent cost.
Negation, transpose and reversal do not increase the exponent.

The predicate `IsTorusRectangleBoxSupport` records the resulting simultaneous
bound for the two original rectangles. For each smooth ambient coefficient,
`exists_torus_rectangle_box_support` chooses a natural number `N` before the
torus exponents, the right integral factor and both rectangles. Nonvanishing at
the actual matrix with `g = torus(lam) * c` puts both rectangles in boxes of
exponent `N + torusSize lam`. The proof applies compact support to
`(-x.transpose)` times the reflected inverse-transpose first Levi block and to
the reversed second rectangle times the second Levi block. It bounds both
transformed compact sets, removes their right factors using bounded inverses,
and takes the maximum of the two constant exponents. Reflected inverse
transpose preserves the common bound, so neither rectangle acquires an
additional torus exponent.

The final theorems prove measurability and the exact product measure of the two
boxes, using the supplied scalar additive Haar measure. If
`D = (m 0 + 1) * k + j * (m 1 + 1)`, the volume at exponent `e` is
`nu(O)^D * (q^D)^e`. This follows from the rectangular box formula and product
measure on rectangles. These are geometric support and volume results; they do
not assert integrability of the coefficient or of its rectangle average.
