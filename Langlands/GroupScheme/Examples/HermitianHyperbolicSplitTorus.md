# Actual closed split tori on several Hermitian hyperbolic planes

This internal construction starts with an actual all-test presentation of a
group scheme by determinant-one isometries of a nonsingular Hermitian matrix
whose full Gram matrix is `MultiHyperbolic.gram M`. It constructs the split
torus with one parameter for each displayed hyperbolic plane.

The parameters are units in the global sections of each actual test scheme.
They enter the tensor coefficient algebra through `includeSections`; quadratic
conjugation fixes them. The diagonal matrix is `diag(t, 1, t⁻¹)`, with each
inverse paired with its own top-block parameter. The earlier diagonal lemmas
prove determinant one, preservation of the entire Gram matrix, and coefficient
naturality for every test restriction.

`torusPoints` lifts these actual matrices through the supplied presentation.
Its naturality gives the group-scheme homomorphism `torusHom` by
`homOfPoints`. Matrix injectivity recovers all top-block parameters. The
inclusion of ground sections into the tensor algebra is injective because
modules over the base field are flat and the scalar inclusion of the extension
field is injective. This proves a monomorphism on all test schemes.

For an affine target locally of finite type, the published closedness theorem
for a monomorphism from an affine torus gives
`isClosedSubgroup_torusHom`. The definition of actual closed-subtorus split
rank then gives `planes_le_splitRank`.

The hypotheses retain arbitrary fields and characteristics. This is an
internal construction from explicit matrix equations and supplied all-test
presentation data; it does not assert that presentation data exists, or use
a classification or the desired split-rank comparison.
