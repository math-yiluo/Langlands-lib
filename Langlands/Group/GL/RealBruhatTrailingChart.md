# Smooth triangular coordinates for real Bruhat cells

`Langlands.GeneralLinear.RealBruhatTrailingChart.RealBruhatTrailingChartStatement`
uses the open chart that multiplies an upper triangular factor by a lower
unitriangular factor. The source consists of coordinate matrices whose diagonal
entries are all nonzero. The upper coordinates encode the upper factor, and
the strict lower coordinates encode the lower factor. The target consists of
invertible real matrices whose trailing principal minors are all nonzero.

The inverse clears each strict lower column using the corresponding trailing
block. The resulting lower unitriangular matrix is the inverse of the desired
lower factor. Uniqueness of the column solves proves both inverse identities.
The forward map is polynomial. The inverse is smooth on the target because
matrix inversion is smooth at invertible blocks.

Right multiplication by the inverse permutation places its Bruhat cell in this
chart. The lower factor is the conjugate of the right unipotent coordinate in
the cell. Its strict lower entries that the inverse permutation leaves below
the diagonal must vanish. Conversely, vanishing of these entries makes the
conjugated lower factor upper unipotent and recovers the given Bruhat cell.

This internal chart calculation extends the Library's upper Bruhat coordinate
identities to an open set of real matrices. It supplies local coordinates for
studying continuous Whittaker functionals supported along Bruhat strata.
