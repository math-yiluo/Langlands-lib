# Full pairing orthogonality of Laurent eigenvectors

This internal helper extends a commutative ring involution coefficientwise to
its additive monoid algebra. Conjugation fixes the monomial exponents. For a
finite Gram matrix, its full preservation equation implies preservation of
the vector pairing conjugate-linear in the first argument and linear in the
second. Neither nonsingularity nor a characteristic restriction is needed.

The pairing of vectors with monomial exponents m and n has exponent m+n and
coefficient equal to the original Gram pairing. If an isometry sends two
constant vectors to those monomial vectors, pairing preservation identifies
this monomial with the constant monomial. When m+n is nonzero, comparing its
coefficient proves that the full pairing is zero.

The Lean proof uses the matrix dot-product identities to transfer the Gram
preservation equation, expands the monomial pairing using multiplication and
finite sums, and compares coefficients. This is derived algebraic infrastructure
for the split-rank comparison, without any assertion that the isometry equation
holds for a particular group-scheme presentation.
