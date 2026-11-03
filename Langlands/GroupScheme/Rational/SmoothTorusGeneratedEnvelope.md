# A smooth connected representative of the envelope of ground-field tori

This internal construction supplies an actual smooth connected closed group
representing `closedTorusEnvelope G` for a smooth affine group over any field.
The ambient group need not be connected or solvable. The construction retains
finite and imperfect fields, arbitrary characteristic, and nonsplit tori.

The proof uses the published pointed-image generation theorem and the published
coordinate-kernel height comparison for smooth connected closed subgroups.
It minimizes the height of the coordinate kernel among smooth connected closed
subgroups whose all-test ranges lie in the fixed torus envelope. This family is
nonempty because the published existence of a closed torus supplies one; every
closed torus lies in the envelope.

For such a minimum subgroup `H` and any closed ground-field torus `T`, the actual
multiplication morphism `H × T → G` is pointed at the identity. Its source is
affine, of finite type, and geometrically integral by the published smooth
connected affine product geometry. Pointed-image generation supplies its smooth
geometrically connected closed generated subgroup `K`. The unit slices show
that `K` contains both `H` and `T` on every test scheme. Every closed subgroup
containing all ground-field tori also contains `H`; it therefore contains this
product morphism and its generated subgroup. Thus `K` still lies in the fixed
torus envelope.

The actual factorization `H → K` is an isomorphism by the published
coordinate-kernel height criterion and the chosen minimum. Composing with its
inverse shows that `T` lies in `H` on every test scheme. Minimality of the fixed
envelope now gives equality of its range with the range of `H`, producing
`exists_smoothConnected_torusGeneratedEnvelope`.

`smoothTorusGeneratedEnvelope` chooses an actual representative, and the two
following theorems record its smoothness and connectedness. The existing
`TorusGeneratedEnvelope` fields provide its closed immersion and equality of
all-test ranges. The argument is an internal derivation from the indicated
published constructions and height comparison. It proves no radical splitting,
quotient existence, or conjugacy theorem.
