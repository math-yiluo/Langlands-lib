# Relative transporter sections in actual identity components

This internal module starts with a smooth affine group scheme over an
arbitrary scheme, two maps of the same standard split torus into that group,
and an actual section satisfying their transporter relation on all
refinements. It also retains the existing section-neighbourhood data,
which place the section in the actual fibre identity components on a
specified open neighbourhood.

For any actual field-valued base map, `fieldIdentityTorusHom` factors the
corresponding actual standard-torus map through the identity component of
the actual group pullback. Its inclusion recovers the given base-changed
map through the canonical split-torus comparison.

The field section point satisfies the transporter relation for the two
base-changed torus maps. The proof uses the exact recovery equation of the
pullback-point equivalence, preserves the all-refinement relation by base
change, and precomposes with the canonical split-torus identification.

If the field point has range in the supplied open neighbourhood,
`fieldIdentityTransporterData` constructs an actual point inside the
actual field identity component. It includes the exact equation recovering
the original field section after inclusion and the all-test transporter
relation for the two torus factors. The relation is reflected through the
monomorphic identity-component inclusion. Disconnected ambient fibres
are permitted.

The geometric specialization uses the exact `geometricPoint S t` of an
original base point `t`. Inclusion and projection of the constructed point
recover `geometricPoint S t ≫ g`, for the original section `g`, as an
equality of scheme morphisms.

The torus factorization respects every automorphism constructed from an
integral character-coordinate equivalence. When the two original maps are
an actual relative torus map and its precomposition with that
automorphism, `fieldAffineIdentityTransporterPoint` gives the resulting
identity-component point in the exact coefficient-point convention of the
rank-one field criterion. Its all-test relation realizes the same
integral-coordinate automorphism on the actual torus in the actual field
identity component.

The provenance is internal: the proofs combine the published
`RelativeIdentityComponent.SectionNeighbourhood` construction with actual
transporter functoriality and canonical split-torus pullback comparisons.
The section and its transporter relation are supplied inputs. The module
does not construct a Weyl element or prove reductivity or openness.
