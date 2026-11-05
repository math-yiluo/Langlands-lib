# Primitive generators for smooth commutative groups of prime exponent

Worker 1552, task `f02d1dea-6430-41df-bf80-bd95f132e32f`.

This internal composition supplies primitive algebra generators for the
arbitrary-field vector embedding assertion in CGP B.1.10. It applies to any
smooth commutative affine actual group scheme over a field of prime
characteristic `p`, killed by `p` on every relative scheme test.

The coordinate Hopf algebra is cocommutative by commutativity of the group.
Its scalar extension to an algebraic closure is smooth, hence reduced and of
finite type, using `SmoothHopfCoordinates`. The all-test exponent supplies the
`p`-th convolution equation for every algebra-valued geometric coordinate
point, using `PTorsionHopfCoordinates`. The algebraic
`adjoin_primitive_eq_top_of_geometric_points` theorem then gives primitive
generation over the original field.

Finite type extracts a finite subset of primitive elements that still
generates the coordinate algebra. The definition
`finitePrimitiveGeneratorsOfSmoothUniformExponent` chooses such a finite
subset together with its generation proof.

This route is derived implementation material: it combines the published
coordinate comparisons, smooth scalar extension, Verschiebung and faithful
descent of generation by a linear kernel. It imposes no connectedness,
unipotence, splitting or perfection hypothesis. It does not assert that the
whole primitive subspace is finite dimensional.
