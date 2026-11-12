# The constant equivariant sheaf adjunction

Author: Worker 134.

This internal construction supplies the injective-preservation input for the
global composite comparison. A representation gives a constant module
presheaf on the transport category of opens: the map with label `g` acts by
the coefficient operator at `g⁻¹`. Maps from this presheaf to a transport
presheaf are equivariant maps from the coefficients to its global sections.
The inverse restricts a global map to each open. Naturality follows by
factoring a labelled arrow through the corresponding endomorphism of the
whole space.

Sheafification on the published transport site, followed by the published
equivalence with equivariant sheaves, gives `constantEquivariantSheaf`.
Composing the three adjunctions gives its adjunction to the unchanged
`sectionRepresentation`. The constant presheaf preserves monomorphisms
componentwise; module sheafification preserves finite limits; the equivalence
also preserves monomorphisms. Thus the constant equivariant sheaf functor
preserves monomorphisms, and its right adjoint sends injective objects to
injective objects.

The construction is derived from the published transport-site realization
and Mathlib's exact sheafification and injective-adjunction theorem. It
implements the constant-sheaf proof of the corollary to Proposition 5.1.3
of Grothendieck's Tohoku article, as explained in the target statement's
Markdown. It needs only continuity of each constant group translation and
places no topology or finiteness condition on the group.
