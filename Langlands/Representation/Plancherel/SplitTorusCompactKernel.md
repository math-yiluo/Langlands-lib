# Compact norm kernels of arbitrary actual split tori

This derived prerequisite transports the published coordinate compactness result
to every actual split torus over an arbitrary-universe nonarchimedean local
field. Both characteristics and rank zero are included. The affine instance in
the interface is supplied by splitness (`IsSplitTorus.isAffineHom` followed by
`isAffine_of_isAffineHom`).

An actual group-scheme isomorphism induces a homeomorphism on rational points
with their canonical `rationalPointTopology`. Its continuous maps are precisely
postcomposition by the underlying morphisms, using the published continuity
theorem. Integer character valuations commute with restriction, so the common
norm kernel maps into the common norm kernel under every morphism. Applying this
to an isomorphism and its inverse identifies the intrinsic kernel with the
homeomorphic inverse image of the coordinate kernel. The latter is compact by
`SplitTorusCompactUnits.isCompact_splitCommonNormKernel` (in the
`Langlands.Plancherel.SplitTorus` namespace).

The published compact-subgroup norm-one argument then applies to any complex
character with open kernel. Smoothness of the actual split torus supplies the
finite-type hypothesis making its canonical point group topological. No
unramifiedness or norm-one hypothesis is imposed on the character.
