# Maximal-torus extensions in affine groups locally of finite type

`maximalTorusExtensionOfFiniteType` chooses an actual maximal torus containing
a given closed torus in an affine group locally of finite type over a field.
Its dependent pair contains the commutative group scheme and its embedding,
together with maximality and a factorization witness for the supplied torus.

The supporting theorem `exists_maximalTorus_extension_of_finiteType` derives
finite Krull dimension of the actual global coordinate ring from
`globalCoordinates_finiteRingKrullDim`. It then applies
`exists_maximalTorus_extension_of_finiteRingKrullDim`. Classical choice packages
the resulting existence proof as data.

This is an internal composition of the coordinate-dimension construction of
Workers 1356 and 1352 with Worker 1352's maximal-torus extension construction.
It introduces no external theorem and has no conjugacy premise. Every field,
all characteristics and imperfect fields are allowed; smoothness,
connectedness and solvability are unnecessary. It supplies a containment
prerequisite, rather than a proof of rational conjugacy.
