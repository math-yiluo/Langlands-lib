# Rank-one stalk spreading for affine quasi-coherent module sheaves

This internal derived module transfers the associated-sheaf spreading theorem to
actual quasi-coherent sheaves on an affine spectrum. It works in every universe
and imposes no noetherian hypothesis.

The first lemma restricts scalars along the canonical isomorphism from the
coordinate ring to the global functions on its spectrum. That function ring is
free of rank one over the coordinate ring. Transitivity of finite presentation
then gives finite presentation of the actual `moduleSpecΓFunctor` object.

For a quasi-coherent sheaf with finitely presented global sections, the actual
`fromTildeΓ` isomorphism transports a rank-one stalk equivalence to the associated
sheaf of those sections. The associated-sheaf spreading theorem places the point
in its open rank-one locus. Invariance under sheaf isomorphisms transports this
membership back to the original sheaf.

`specRankOneTrivializingNeighbourhood` uses classical choice to select an actual
open containing the original point, with a proof that the actual restricted
sheaf is isomorphic to the structure module. It asserts no compatibility between
this choice and the given stalk equivalence.

This is a composition of the imported Library results and Mathlib's canonical
affine comparison and finite-presentation transitivity; it imports no additional
literature claim. The input here is quasi-coherence and finite presentation of
global sections on `Spec R`. Passage from a sheaf that is merely locally finitely
presented on an arbitrary scheme is a separate local reduction.
