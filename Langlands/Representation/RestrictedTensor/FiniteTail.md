# Finite coordinates and reference tails

This internal algebraic construction separates an element of the actual cofinite
restricted product into its coordinates on a finite set and its entire
complementary tail. It uses the published `finiteAssemble` and
`complementProjection` constructions. It assumes groups and reference subgroups,
with independent index and group universes, and requires no topology.

`finiteProjection H S` and `tailProjection H S` are endomorphisms of the actual
restricted group. Their coordinate formulas retain the original coordinate on
`S` and its complement, respectively, and give the identity elsewhere. Their
product, in either order, is the original element. More generally, a finite
projection commutes with any tail projection for the same finite set because
their coordinate supports are disjoint.

The finite projection is the identity element when the finite set is empty.
`finiteProjection_insert` gives the finite induction rule: adding a fresh
coordinate multiplies the previous projection by the actual Mathlib singleton
insertion at that coordinate. These proofs use coordinate extensionality and
do not assume that the local groups commute.

`tailProjection_mem_tailReferenceSubgroup` identifies the complementary
projection as a member of the full reference tail when the original element
lies in its reference subgroups outside `S`. This includes tails with infinitely
many nonidentity coordinates. `exists_finset_reference_outside` enlarges any
given finite set to ensure this condition, using the defining cofinite property
of the restricted product.

For a representation over a commutative ring, the final lemma
`apply_eq_finiteProjection_of_tail_fixed` says that an element acts on a
tail-fixed vector through its finite projection whenever its complementary
coordinates are in their reference subgroups. The proof factors the group
element, applies multiplicativity of the representation, and removes the
tail action by the supplied fixedness. The coefficient and carrier universes
are independent; no admissibility or irreducibility is needed.

This module is a preparatory algebraic API for the full-group equivariance
argument in restricted-tensor factorization. It constructs no tensor evaluation
map and claims no factorization theorem. The definitions and proofs are internal
consequences of the existing restricted-group operations, not a transcription of
a separate result in the literature.
