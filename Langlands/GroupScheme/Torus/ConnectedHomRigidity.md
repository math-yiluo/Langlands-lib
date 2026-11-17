# Detecting split-torus homomorphisms on one fibre

This internal helper derives a consequence of the published split-torus
homomorphism-family rigidity theorem. It concerns actual morphisms over a
preconnected scheme and an arbitrary field-valued point of that scheme.

The construction `fieldFibreCharacterMap` takes an actual homomorphism, pulls
it to the specified field, identifies its endpoints with the coordinate tori
through their canonical base-change isomorphisms, and returns the resulting
integral character pullback. It is defined without a connectedness hypothesis.
The rigidity results below recover the whole actual map from this constructed
linear map when the original base is preconnected.

The proof forms the pointwise quotient of two homomorphisms as a homomorphism
family. Equality on the specified fibre says that its exponent matrix is zero
at the image point. The open-and-closed exponent locus is constant on the
preconnected base, so the quotient is the identity on every test scheme.
The actual pullback point equivalence transfers the fibre hypothesis to
tests factoring through that field point.

Consequently, base change along the field-valued point is injective on the
actual hom set. The source and target are the coordinate split tori attached to
any two finite indexing types. No reducedness or affineness hypothesis is
needed; preconnectedness and the specified field-valued point suffice.

The module also recovers every such homomorphism from the integral character
map of its field fibre. The fibre is identified with the two coordinate tori
using the canonical base-change isomorphisms. Extend its integral character
map by the published `exponentHom` construction. That construction commutes
with base change and recovers the original fibre homomorphism by
`exponentHom_characterMap`, so fibre detection gives equality with the original
map over the whole base.

This equality gives the exact pullback formula for every fixed-exponent
character as an equality of actual group-scheme morphisms, and hence on every
test scheme. In the automorphism case, the given automorphism is exactly
`fieldAutomorphismExtension` applied to its canonically identified field fibre.
The proofs use the published integral-coordinate construction and its character
formula; they do not require a separate exponent-matrix uniqueness theorem.

These are internal consequences of `HomFamilyRigidity` and
`ExponentHomomorphisms`. They supply connected-base torus rigidity for the
pinned-automorphism argument. They do not assert that an arbitrary automorphism
of a reductive group preserves a torus or assert a pinned factorization.
