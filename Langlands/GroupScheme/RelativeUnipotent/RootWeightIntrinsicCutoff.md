# Intrinsic cyclic cutoffs for actual root-weight charts

This derived module identifies actual root-chart coordinate cutoffs with intrinsic
cyclic weight subgroups on every coefficient algebra, over an arbitrary
commutative base ring. It uses `RootWeightPolynomial` and the direct monomial
criterion `NonnegativeCyclicCoordinates`.

`TorusAction.alongCocharacter` restricts any split-torus action to a specified
integral cocharacter, expressed as a rank-one split-torus action. Its homogeneity
theorem proves that a character ch becomes the integer pairing of ch with that
cocharacter. This is an identity of actual algebra-point actions.

For a root-height chart C with actual torus-equivariant ambient root labels,
`polynomialVariable_counit` proves that its polynomial variables vanish at the
identity. It uses the chart's zero ordered root product and the affine section
comparison, rather than treating the chart as an additive homomorphism.
`cyclicCoordinates` constructs the actual nonnegative cyclic-coordinate data
from C whenever a supplied cocharacter realizes the supplied natural root
weights. Its polynomial evaluation map is the identity, so its surjectivity is
proved without an additional coordinate hypothesis.

`mem_intrinsic_cutoff_iff` proves that an affine point of the chart group belongs
to the intrinsic cyclic cutoff r precisely when all original root coordinates
of weight less than r vanish. The coefficient algebra may have nilpotents; only
r > 0 is required.

`mem_intrinsic_scaled_iff` applies this to a `RootWeightData` W whose root pairings
are q times the original weights, for a positive natural q. At intrinsic cutoff
q*(d+1), the subgroup is exactly W.subgroup d on that affine test scheme. Thus a
multiplier in a realizing cocharacter changes the intrinsic cutoff parameter;
the original represented filtration and its unscaled weights are unchanged.

This module's final comparison is on all coefficient algebras, not yet a claim
of coordinate-independent ambient subgroup equality on arbitrary scheme tests.
That extension, comparison across different chart groups or maximal tori,
parabolic normalization and global descent remain obligations in Task 7200.
