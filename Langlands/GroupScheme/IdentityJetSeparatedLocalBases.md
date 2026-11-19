# Finite local bases of separated smooth identity jets

For a smooth separated group scheme over an arbitrary base,
`IdentityJet.finiteLocalFrames_of_separated` chooses finite local
frames of the pushforward of the structure sheaf of the actual
identity jet of order `n`.

The proof starts at a base point with an affine open of the base and an
affine open of the group above it containing the identity point.
Shrink the base to a basic open on which the section lands in that
group chart. Intersect the chart with the inverse image of the basic
open under the structure morphism. This intersection is a basic open
in the group chart and its pullback along the identity section is
exactly the chosen base open.

The jet sections over that chart are the quotient of its coordinate
algebra by the `(n + 1)`st power of the kernel of the augmentation
induced by the section. The coordinate algebra is smooth over the
base chart. The Library's algebraic section jets make this quotient
finite projective as a module, giving flatness and finite presentation
of the chart ring map. These charts cover the jet because the base
surjects onto its points via the lifted section. Theorems
`IdentityJet.flat_projection` and
`IdentityJet.locallyOfFinitePresentation_projection` give the two
properties for the projection.

By `IdentityJet.finite_projection`, the inverse image of any affine
open of the base is affine and its ring of functions is finite over
the base ring. Flatness and finite presentation as an algebra make
this ring a finitely presented flat module, hence projective. The
pushforward along the finite projection is quasi-coherent.
`IdentityJet.hasFiniteLocalBasis_of_separated` therefore applies the
Library's finite projective affine-sections criterion to this
pushforward. The choice of frames uses the resulting local bases.

This is an internal extension of the Library's affine-group
construction of identity jet frames to separated smooth ambient
groups.
