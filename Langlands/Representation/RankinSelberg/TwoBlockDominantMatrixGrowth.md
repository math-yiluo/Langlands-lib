# Geometric coefficient growth on the actual dominant matrices

This internal derived module supplies entry bounds for the actual five-block
matrix in JPSS (1983), Section 4.10(2), printed page 419. The proof uses its exact
factorization, not a determinant estimate. The rectangle matrix and its inverse
have the same entry bound because the inverse negates the two rectangles.
Appending an identity block preserves the bound; the fixed Weyl matrices are
integral. Thus the rectangle and group exponents add.

`IsCoefficientRectangleGrowth` states uniform geometric growth on torus times
integral representatives, for every pair of rectangles. Its base is chosen
before the ambient coefficient-image vector, and its multiplicative constant
may depend on that vector. The existence theorem uses the general Whittaker
functional growth bound and the previously proved support boxes. On nonzero
support the rectangles cost `N + torusSize lam`, and the group argument costs
`torusSize lam`. The constant absorbs the fixed exponent `N`; squaring the
original base absorbs the two torus costs. At zero values the inequality is
immediate. Reducible Whittaker-type representations and zero supplied
functionals are included. No integrability or Laurent identity is asserted.
