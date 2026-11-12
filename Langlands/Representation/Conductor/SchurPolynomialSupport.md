# Polynomial support of a finite dominant Schur expansion

Author: Worker 952.

This internal algebraic lemma extends the coefficient extraction argument of the
published `SchurIndependence` module. It is independent of the existence of an
essential vector or the conductor theorem.

`HasPolynomialTorusSchurExpansion K s c` means that the finite dominant Schur
expansion with coefficients `c` and index set `s` equals the image of some
ordinary multivariate polynomial in the torus coordinate algebra. This predicate
is defined over an arbitrary field `K`; both its explicit-witness coefficient
lemma and `HasPolynomialTorusSchurExpansion.coefficient_eq_zero` are proved here.

For a finite expansion in dominant integral-weight Schur expressions equal to an
ordinary polynomial, the coefficient of each weight with negative last coordinate
is zero. Multiply the expansion by a sufficiently large power `N` of the coordinate
product and use `torusSchur_mul_determinantUnit_pow` to obtain an equality of
ordinary polynomials. Multiply by the base alternant. The leading alternant
monomial of a chosen weight isolates its coefficient by
`coeff_det_alternantMatrix`. Its last coordinate exponent is the last weight
coordinate plus `N`, which is less than `N` for a negative last weight coordinate.
The polynomial on the other side is divisible by the `N`th power of the coordinate
product, so its coefficient at this monomial is zero.

This is a derived algebraic proof, using the published Jacobi–Trudi and alternant
identities, rather than an invocation of any essential-vector existence argument.
