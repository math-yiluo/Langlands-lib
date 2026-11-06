# Matrices of the binary homogeneous polynomial representation

This internal derived construction writes the actual degree `m` homogeneous
polynomial representation of `SL(2,R)` in the monomial basis `binaryBasis m`.
Here `R` is any commutative ring and `m` is any natural number.
`binaryMatrixRepresentation m` is the monoid homomorphism obtained by composing
the actual homogeneous representation with the algebra isomorphism that takes
linear operators to their basis matrices.

For row `r` and column `c` in `Fin (m+1)`, the upper root at parameter `t`
has entry `choose (m-c) (r-c) * t^(r-c)` when `c <= r`, and zero otherwise.
The lower root has entry `choose c (c-r) * t^(c-r)` when `r <= c`, and zero
otherwise.

The proof uses the arbitrary monomial formulas in `BinaryPolynomialRootActions`
and coefficient extraction in `BinaryHomogeneousBasis`. In each binomial sum,
only the term of the required zeroth exponent contributes to a fixed matrix
entry. The index bounds justify the subtraction and establish that this term
lies in the summation range. All formulas include `m=0`.

The provenance is elementary derived algebra. These matrices describe actual
group elements acting on the actual homogeneous submodule. This file does not
claim irreducibility or identify an induced coordinate representation.
