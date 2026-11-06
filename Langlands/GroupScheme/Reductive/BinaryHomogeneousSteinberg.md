# Steinberg irreducibility on binary homogeneous polynomials

This internal derived unit constructs `binaryHomogeneousEquiv m`, an actual
`Representation.Equiv` from the special-linear action on the entire submodule
`MvPolynomial.homogeneousSubmodule (Fin 2) R m` to `binaryRepresentation m`,
for every commutative ring `R` and natural degree `m`. Its underlying linear
equivalence is `(binaryBasis m).equivFun`. Thus its coordinate at `c` is precisely
the coefficient of `X 0 ^ c * X 1 ^ (m-c)`.

The intertwining identity follows from Mathlib's basis-matrix identity
`LinearMap.toMatrix_mulVec_repr`: multiplying the matrix of a linear map by the
coordinates of a vector gives the coordinates of its image. Both representations
here were constructed from the same actual matrix-column substitution.

For an infinite field `k` of prime characteristic `p`,
`binaryHomogeneous_isIrreducible p s` proves that the actual special-linear
representation on the full homogeneous submodule of degree `p^s-1` is irreducible
for every natural `s`. The proof uses `binaryRepresentation_isIrreducible` and
transfers simplicity along the group-algebra linear map of the constructed
bijective intertwiner. It includes characteristic two and degree zero; no
irreducibility or root-realization premise is supplied.

This is elementary transport of the previously constructed rank-one action and
its irreducibility proof. It neither identifies a full induced coordinate space
nor proves the higher-rank Steinberg big-cell statement.
