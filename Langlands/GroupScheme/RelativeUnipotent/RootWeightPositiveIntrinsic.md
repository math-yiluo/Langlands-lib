# Intrinsic cyclic filtrations on the actual positive subgroup

This derived module defines the intrinsic cyclic filtration inside the actual
represented positive subgroup W.groupScheme 0, with its original induced group
law. The arbitrary commutative base ring and every scheme test are retained.

`toTermPolynomialModel` is an actual group-scheme homomorphism to the explicit
polynomial corepresentation, obtained from the published affine-corepresentation
comparison. Its underlying map is the identity of the term's coordinate affine
space. The coordinate theorem proves that reading any point through this model
retains the term's own coordinate functions.

`positiveIntrinsicCutoff` pulls the represented intrinsic cyclic weight subgroup
back through this actual homomorphism. It is a subgroup functor on the positive
subgroup itself. This construction does not require an ambient conjugation to
preserve the auxiliary full regular root-chart group.

`mem_comap_zeroInclusion_iff` expresses the original W.subgroup d, restricted to
W.groupScheme 0, in its own supported coordinates. Indices omitted from the
positive support are already zero by the actual coordinate inclusion formula.

For a cocharacter realizing q times the original secondary weights with q > 0,
`mem_positiveIntrinsicCutoff_iff` applies the actual positive polynomial data from
`RootWeightTermPolynomial` to identify the intrinsic cutoff q*(d+1) with those
same low-coordinate equations. Thus `positiveIntrinsicCutoff_eq_comap` proves
equality of subgroup functors with the original W.subgroup d pulled back along
W.inclusion 0, on every scheme test. The filtration weights and the original
cutoff d+1 remain unscaled.

This identifies the intrinsic filtration on the appropriate actual positive
object. Constructing and checking equivariance of ambient conjugation or
change-of-torus maps, proving parabolic normalization, and effective descent
remain separate steps of the finite vector-bundle filtrations of supplied
relative radicals.
