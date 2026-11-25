# Homogeneous polynomial coordinates on the actual positive terms

This derived module constructs homogeneous polynomial-coordinate data on the
actual represented filtration terms themselves, over the arbitrary commutative
base ring. It uses the actions of `RootWeightTorusAction` and the coordinate
inclusion equations of `RootWeightQuotient`.

For every term d, `termChart` identifies its literal underlying affine-space
scheme with itself. `termPolynomialCorepresentation` corepresents the actual
induced group law by this polynomial ring; it does not replace the induced group
law with addition. The algebra coordinates agree with the term's standard
coordinates after the affine section comparison.

`term_coordinates_torusAction` proves exact root-character scaling for those
standard coordinates on every scheme test. It follows by reading the ambient
root-coordinate action at the retained index and using `coordinates_inclusion`.
The corresponding polynomial variables are homogeneous for
`termPolynomialTorusAction` on every coefficient algebra. The actual group
identity has zero coordinates, so every variable has zero augmentation.

For term zero, `positiveTermCyclicCoordinates` constructs the nonnegative cyclic
polynomial-coordinate data from a supplied cocharacter whose root pairings are
q times the original secondary weights. Its generators are all the polynomial
variables and their evaluation map is the identity. If q > 0, the module proves
that every retained variable has strictly positive weight, since the coordinate
support of term zero retains exactly the strictly positive secondary weights.
The empty-coordinate case is included.

The construction works on the actual positive subgroup, so it can be used when
a later ambient conjugation preserves that subgroup but does not preserve the
auxiliary full regular root-chart group. This module does not construct that
conjugation, prove its equivariance, or supply the remaining change-of-torus and
descent arguments of the finite vector-bundle filtrations of supplied relative
radicals.
