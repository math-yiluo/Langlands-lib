# Smooth stabilizer directions along a real Bruhat cell

`Langlands.Global.RankinSelbergGlobal.RealBruhatGeneratorField.RealBruhatGeneratorFieldStatement`
constructs a smooth paired root direction throughout the product chart for a
real Bruhat cell with an adjacent ascent. The field vanishes on the cell and
its derivative at every cell point is nilpotent.

The proof writes the zero-section point as an upper triangular factor times
the permutation times an upper unipotent factor. The upper factor comes from
the upper entries of the chart matrix. The right factor is the conjugate of
the lower unitriangular chart factor, and the zero normal entries give its
upper triangularity. Matrix inversion is smooth on the two invertible
factors, so their conjugated root generators vary smoothly. Applying the
inverse chart derivative to the corresponding left and right matrix
directions gives the paired field. The pointwise stabilizer identity makes
this field zero along the cell.

The tangent derivative therefore vanishes. Along a normal direction the two
generators are constant, and the product-rule term from differentiating the
inverse chart derivative is zero at the cell point. The normal component of
the remaining term is the nilpotent endomorphism from
`RealBruhatNormalAction`. A power of the full derivative thus lands in the
tangent space, and one more application kills it. The companion trace
identity follows from nilpotence.

This internal result supplies the varying stabilizer direction used for
transverse derivatives on lower Bruhat cells.
