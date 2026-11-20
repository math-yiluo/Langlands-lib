# The Brauer period divides the reduced degree

For a semilinear action on a full matrix algebra, `determinantCochain` takes the
determinants of the chosen invertible lifts. Applying the determinant to the
published scalar-defect formula yields `scalarDefect_pow_card`. Coefficient
automorphisms commute with the determinant, and a scalar matrix of size \(d\)
has determinant equal to the \(d\)-th power of its scalar. Thus the \(d\)-th
power of the factor set is the coboundary of the determinant cochain. In
additive cohomology this gives `card_nsmul_descentClass`.

`Brauer.addOrderOf_classOf_dvd_reducedDegree` evaluates the absolute Brauer
comparison on its finite Galois splitting chart of size equal to the reduced
degree. Inflation carries the annihilation of the relative class into
continuous cohomology. Injectivity of the comparison then gives annihilation
in the actual Brauer group, which is equivalent to the asserted divisibility.
The base field and algebra carrier are in the common universe of the published
Brauer group.

This is an internal consequence of the published Brauer comparison and the
matrix determinant. The scalar-defect convention is the one documented in
`Relative.md`, from Serre, *Local Fields*, Chapter X, §5.
