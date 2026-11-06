# Homogeneous row polynomials as special-linear coordinates

This derived construction substitutes one row of the universal determinant-one
matrix into an ordinary multivariate polynomial. Its specialization at every
matrix is evaluation at the corresponding matrix row. The homogeneous
restriction intertwines the actual homogeneous polynomial action with pullback
by right multiplication in the special linear group.

For binary polynomials over any integral commutative ring, the entire polynomial
ring embeds by the bottom row. To prove injectivity, the implementation
specializes the universal matrix into the fraction field of the binary
polynomial ring at the determinant-one matrix with rows
`[Y⁻¹, 0]` and `[X, Y]`. On bottom-row polynomials this specialization is the
injective fraction-field map. This also proves injectivity on every full
homogeneous polynomial submodule.

The provenance is elementary polynomial and quotient algebra, the existing
homogeneous substitution, and the defining injectivity of the fraction field.
These embeddings do not yet identify an entire covariant coordinate space.
