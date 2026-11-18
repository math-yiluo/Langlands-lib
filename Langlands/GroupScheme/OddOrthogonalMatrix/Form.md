# The split odd-dimensional scalar quadratic form

This internal construction appends the square `z²` to the Library's split even
hyperbolic form `∑ᵢ xᵢyᵢ`. Its coordinate index is `Unit ⊕ (l ⊕ l)` for a finite
type `l` in `Type`, so its dimension is `2 * Fintype.card l + 1`. The ground
field has arbitrary universe `u`.

The representative is the block matrix `diag(1,Q)`, where `Q` is the published
split even representative. Its polar matrix is `diag(2,J)`, and multiplication
by this matrix exchanges the hyperbolic halves while multiplying the axis
coordinate by two. Consequently its kernel is the axis in characteristic two
and is zero otherwise. The dimension is exactly one or zero respectively.

For the quadratic radical, polar orthogonality first kills every hyperbolic
coordinate. The remaining quadratic equation is `z² = 0`, which implies
`z = 0` over every field. This proves zero quadratic radical without a
characteristic or perfection restriction.

The construction and proofs are internal block-matrix consequences of
`OrthogonalMatrix.formMatrix` and the scalar-involution conventions. They
introduce no new literature translation. This module only constructs a
split quadratic form and verifies its linear algebra; identifying the
corresponding group with an arbitrary type-B form remains separate work.
