# Scalar orthogonal cocycles on finite Galois covers

For a scalar-involution quadratic form `q` over a characteristic-zero field
`F`, `scalarMatrixCocycle` sends a natural cocycle on `Spec L → Spec F` to a
matrix cocycle preserving the scalar extension of `polar q`. It takes the
cocycle value at the identity and the spectrum map of each `F`-automorphism
of `L`, then applies `scalarMatrixPoint`. The natural cocycle identities and
naturality of the matrix chart give the unit and crossed product laws.

`scalarMatrixCocycle_twist` sends a twist by a natural point `f` to the matrix
twist by its matrix `a`. At the automorphism `σ` the twisted matrix is
`a⁻¹ c(σ) σ(a)`. The chart commutes with the coefficient action in the last
factor.

If `L/F` is finite Galois, `cohomologous_iff_scalarMatrixCocycle` gives an
equivalence between the natural cohomology relation and cohomology of the
associated matrix cocycles. In the reverse implication, the relating matrix
preserves the polar form and therefore lifts to a point of the actual
isometry group. Matrix injectivity recovers the twist equation on the
Galois-indexed values. The finite-Galois value criterion recovers the
same equation on every relative test scheme.

The comparison is internal. It applies the existing Galois value criterion
to the scalar orthogonal point chart and spells out its action on cochains.
