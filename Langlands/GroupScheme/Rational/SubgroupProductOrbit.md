# Subgroup products as actual scheme orbits

Worker 1556.

This internal construction expresses a product of two subgroup presentations as
an orbit of their actual product group. Over any base scheme, the action sends
`((v,c),x)` to `j(v) x c(c)⁻¹`. Its action laws follow from the existing
test-scheme group laws and associativity, with no normalization assumption.

The acting group's stabilizer at the identity is the diagonal map from the
existing scheme-theoretic `subgroupIntersection j c`. Its represented range is
characterized by equality of the two ambient images on every scheme test.
The orbit-fiber theorem identifies equality of orbit points with right cosets
of this actual diagonal stabilizer, including on nonreduced tests.

If the second subgroup is closed and its source is separated over the base,
the diagonal stabilizer is a closed subgroup of the product: its composite
with the first projection is the closed pullback inclusion, and that projection
is separated.

Over an algebraically closed field, `closedOrbitQuotient` applies the existing
`SchemeAction.quotientOfClosedAffineOrbit` to this action and stabilizer.
The two factors must be smooth and affine, the ambient group affine and locally
of finite type, and the actual intersection smooth. Closedness of the orbit
is an explicit premise. The resulting quotient scheme is the actual schematic
orbit image, with a smooth, surjective, quasi-compact projection and the
all-test coset-fiber identity.

The provenance is direct construction using the Library's categorical product
groups, scheme actions built from all-test laws, actual intersection pullback,
original ambient group law, and closed-affine-orbit quotient construction.
No finite-field product-surjectivity, dimension, or normality conclusion is
asserted here; orbit closedness remains a premise of the quotient construction.
