# Commutator and polynomial directions at a regular matrix

This is the linear algebra used in the local conjugation argument for
`Langlands.BaseChange.NormNeighbourhoodStatement`. Its role in the norm
openness argument corresponds to the use of a maximal torus in
Henniart and Lemaire (2011), II.2.10, printed page 71.

For a matrix with separable characteristic polynomial, the algebraic closure
contains exactly `n` distinct eigenvalues. Corresponding eigenvectors form a
basis. In that basis, each off-diagonal entry of a prescribed matrix is a
commutator entry, found by dividing by the corresponding eigenvalue difference.
The diagonal entries are obtained by a polynomial of degree less than `n`.
The proof solves for its coefficients by the invertible Vandermonde matrix.

After changing back to the original basis, an `F`-linear retraction of the
algebraic closure onto `F` projects the solution to the base field. Applied
entrywise, the retraction commutes with multiplying on either side by a matrix
over `F`. It also projects the polynomial coefficients. This gives
`exists_commutator_add_powers` over `F`.
