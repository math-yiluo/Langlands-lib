# Counting monic polynomial factorizations of fixed degree

`PolynomialLabel k` collects the monic irreducible polynomials over `k` other than `X`, with degree as their weight. Its degree fiber is the published `irreduciblePolynomialLabels` subtype. Every label has positive degree. Its constant coefficient is nonzero because divisibility by `X` would make the two monic irreducibles equal.

Multiplying the entries of a weighted multiset gives a monic polynomial of the specified degree with nonzero constant coefficient. Applying normalized factorization to such a product recovers its monic irreducible factors with their multiplicities. Conversely, the normalized factors of a monic polynomial with nonzero constant coefficient are labels, and their product is the original polynomial. This gives `polynomialFactorMultisetEquiv`, including the empty factorization in degree zero. Over a finite field the types are finite by the degree bound on polynomials.

In degree `n+1`, reading the constant coefficient as a unit and the next `n` coefficients as field elements gives `monicNonzeroConstantCoeffs`. The inverse uses a sum of the corresponding monomials with leading term `X^(n+1)`. Coefficient extraction verifies the two inverses. The cardinality is `Nat.card kˣ * Nat.card k ^ n`.
