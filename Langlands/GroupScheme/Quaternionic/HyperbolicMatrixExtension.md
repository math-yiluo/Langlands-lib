# Matrix extension along an actual hyperbolic plane

Authors: Worker 124.

This internal construction extends a binary matrix along the actual hyperbolic
plane of a quaternionic quadratic form and acts as the identity on the polar
orthogonal complement. It uses row vectors throughout.

For rectangular matrices `E` and `R` with `E R = 1`, the extension of `M` is
`R M E + (1 - R E)`. Direct multiplication proves that this is a unital
monoid homomorphism. It gives a homomorphism on actual matrix units.
Restriction by `E` and `R` recovers `M`, so the unit homomorphism is injective.
Its formula commutes with every coefficient-ring homomorphism.

For an actual hyperbolic pair `e,f`, `planeInclusion` has these two rows and
`planeRetraction` uses the polar coordinates `h(v,f),h(v,e)`. Their product is
the binary identity. The induced unit extension acts by the prescribed binary
matrix on the plane and fixes the hyperbolic remainder. Pulling back the
actual quotient-valued quadratic form gives the canonical binary hyperbolic
form, proved using vector-value detection and the hyperbolic value formula.

These are derived matrix and form constructions from the Library's hyperbolic
decomposition and rectangular pullback APIs. No external-source correspondence
is claimed. They do not yet identify the extension with a subgroup of an
arbitrary supplied spin cover or prove equality of the two spin kernels.
