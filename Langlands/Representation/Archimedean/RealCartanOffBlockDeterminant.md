# Normalized off-block determinants

For invertible real square blocks `g` and `h`, `offBlockAction g h` maps a rectangular
block `X` to `g⁻¹ X h`. Its inverse sends `X` to `g X h⁻¹`. In the matrix-unit basis, the
entry at row `(i,j)` and column `(p,q)` for `X ↦ A X B` is `A i p * B q j`. This is the
Kronecker product of `A` with the transpose of `B`. The determinant therefore has the
block determinant of `g⁻¹` with multiplicity the size of `h`, and the block determinant
of `h` with multiplicity the size of `g`.

Swapping the roles of `g` and `h` transposes the coefficient matrix of the inverse action
and exchanges its two coordinate labels. Transpose and simultaneous reindexing preserve
the determinant of the action and of the identity minus the action. For an invertible
endomorphism `L`, the factorization `1 - L⁻¹ = -L⁻¹ (1 - L)` contributes the factor
`|det L|⁻¹` to the absolute determinant. The square root of the absolute determinant of
the action changes from `√|det L|` to its reciprocal. These two changes cancel in
`normalizedOffBlockDet`, as stated by `normalizedOffBlockDet_swap`.

This internal matrix identity gives order independence for the normalized contribution of
a pair of blocks to the regular Cartan calculation. It applies to any two invertible blocks.
