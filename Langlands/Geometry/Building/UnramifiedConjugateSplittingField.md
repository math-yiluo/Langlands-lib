# Conjugating embedded splitting fields

This internal construction transports intermediate fields across a commuting
square of field isomorphisms. The image subfield contains the target base
field because the base isomorphism is surjective. Restricting the ambient
isomorphism gives a ring equivalence on the intermediate field, and its
compatibility with the base maps is proved after embedding into the ambient
target field.

Finite dimensionality transfers by equipping the target temporarily with
scalars from the source base, applying the induced algebra equivalence, and
then extending the scalars to the target base. Galoisness transfers by
Mathlib's theorem for compatible isomorphisms of field extensions.

These constructions are derived from Mathlib's intermediate-field images,
algebra equivalences, finite-module transfer and Galois transfer. The current
module does not yet assert that a conjugated torus splits over this image
field or construct a conjugated zero datum.

Finite dimensionality is transported by Mathlib's existing
`Module.Finite.of_equiv_equiv`, specialized to the two field extensions.
