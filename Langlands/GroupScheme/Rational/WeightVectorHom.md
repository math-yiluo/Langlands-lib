# Homomorphisms between vector groups of the same torus weight

This internal comparison extends the existing uniqueness argument for weight
vector coordinates to equivariant group-scheme homomorphisms. It is derived from
the published universal polynomial and Laurent tests in `WeightVectorUniqueness`
and the actual dual-number comparison in `VectorPointLieEquiv`. It makes no
independent literature claim.

Let a split torus over a field act on two group schemes with natural finite
vector coordinates of the same nonzero character. Their dimensions can differ.
An equivariant group-scheme homomorphism commutes with scalar multiplication in
these coordinates on every test scheme, as proved by
`coordinateSmul_equivariantHom`. No affineness or invertibility of the
homomorphism is assumed for this conclusion.

The proof first treats the universal scalar and an arbitrary point of a
universal polynomial test. A cocharacter pairs positively with the nonzero
character. Pulling back along the injective map sending the scalar to a positive
power of a Laurent variable turns scalar multiplication into torus action on
both sides. Equivariance proves equality after pullback, and injectivity on
global functions cancels that pullback. The classifying map for an arbitrary
scalar and vector then proves the assertion on every test.

When both groups are affine, `vectorPointLieEquiv_equivariantHom` proves that
the homomorphism's actual differential intertwines their point-to-Lie maps on
every commutative coefficient algebra, including nonreduced algebras. The
point-to-Lie map is epsilon times the constant point in the vector scalar
structure. The scalar compatibility just proved and naturality of the constant
point establish the differential identity.

`weightVectorHomLinearMap` expresses the actual differential as a linear map
between the two coefficient vector spaces. Its coordinate formula proves that,
under the common nonzero weight and equivariance hypotheses, the same linear
map computes the original homomorphism on actual points.

These conclusions concern common-weight homomorphisms. They do not identify a
Bruhat–Tits filtration or establish the root-depth special-fibre kernel theorem.
