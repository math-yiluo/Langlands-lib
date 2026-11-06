# Actual transporter points in relative cocharacter centralizers

This internal adapter factors an actual transporter point through an actual
relative cocharacter centralizer. The base is the spectrum of an arbitrary
commutative ring in an arbitrary universe. The ambient group is affine, and its
fibres may be disconnected. Smoothness, reductivity and closedness of the supplied
torus map are not required for this factorization.

Fix a finite standard torus, its actual map `i` into the ambient group, an integer
cocharacter vector `n`, and an integral linear automorphism `e` of the character
coordinates. Assume that the resulting actual automorphism `exponentIso e` fixes
the actual `exponentCocharacter n`. The fixing assumption is equality of actual
group homomorphisms over the entire base. For an arbitrary test scheme `T`, the
input point `g` is an all-test transporter from `exponentIso e` followed by `i`
to `i`: on every refinement and every torus point, the first map evaluated at
that point multiplied by `g` equals `g` multiplied by the second map's value.

`transporterPoint` constructs an actual `T`-point in
`RelativeCocharacterCentralizer.groupScheme I G i n`.
`transporterPoint_comp` states that composing with the specified centralizer
inclusion recovers exactly the original over-morphism `g`.
`transporterPoint_isTransporter` proves the same all-test transporter relation
for the centralizer's actual `torusHom`, with the same automorphism `e`.
`transporterPoint_naturality` proves compatibility with every refinement of `T`.
Consequently the recovery equality also retains the original point when `T` is
a residue-field or geometric-field test scheme.

The general helper
`PointwiseSchemeAction.IsTransporter.mem_centralizer_of_fixed_cocharacter`
works over an arbitrary scheme, for an arbitrary source group homomorphism `c`
fixing a specified cocharacter; invertibility of `c` is unnecessary. It
precomposes the transporter relation with that cocharacter. The two resulting
maps coincide by the fixing equation. Evaluating the relation on the universal
product test `T × Gm` proves that the conjugation orbit is constant, which is the
actual dynamic centralizer membership condition.

The construction then applies the inverse point equivalence for the published
represented relative centralizer. Its inverse equation gives exact recovery.
Monicity of the inclusion reflects the original transporter relation into the
centralizer and proves naturality by cancellation.

The provenance is internal: these are formal consequences of the published
all-test transporter relation, represented-subgroup point equivalence, and actual
relative cocharacter centralizer construction. This module supplies a point
factorization; it does not by itself construct an etale lift or prove openness of
the reductive identity-component locus. For a smooth ambient group the published
relative centralizer is smooth, so the resulting prescribed residue-valued point
can be supplied to the separate pointed transporter lifting construction.
