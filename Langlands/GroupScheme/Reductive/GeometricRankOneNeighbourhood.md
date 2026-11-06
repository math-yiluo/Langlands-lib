# Actual rank-one neighbourhoods from a geometric Weyl transporter

This internal construction removes the local-section premise from the
relative rank-one neighbourhood step. It constructs an actual good open of
the original affine base from an actual transporter point in the original
geometric identity component. It still retains the original rank-one root
profile and weight-line data explicitly, and does not claim the final
general openness theorem.

Let a smooth affine group scheme over any commutative ring have a supplied
closed standard split torus. Fix an original base point where its torus in
the actual geometric identity component is self-centralizing. The full
actual root support there must be exactly a specified nonzero integral
character vector and its negative; the corresponding actual relative
weight ranks must both be one. An integral character-lattice automorphism
must invert this vector.

The remaining input is an actual point of that original geometric identity
component satisfying the all-test transporter equation for the actual
geometric torus and the specified integral-coordinate automorphism. No
rational residue point, finite-separable residue extension, local section,
or etale local model is an input.

The proof first composes this point with the actual identity-component
inclusion into the original geometric fibre. Mapping its transporter
equation through that group homomorphism gives the equation for the actual
geometric-fibre torus. Precomposing the torus source with the canonical
split-torus base-change isomorphism, and using exact base-change
compatibility of `exponentIso`, converts this to the equation for the two
actually pulled-back original homomorphisms. The point itself is retained.
Its range lies in the actual fibre identity set because it factors through
the actual identity-component inclusion.

The geometric point maps the unique point of its algebraically closed
residue-field spectrum to the original base point. Apply the actual
`etaleIdentityTransporterOfSplitTorus` construction to the point just
obtained. It produces an affine etale neighbourhood whose image contains
the original point, together with an actual all-test transporter section
in the actual relative identity component after base change. This step
chooses a section; recovery of the original geometric point is unnecessary
and is not asserted.

Choose a point of that affine neighbourhood above the original base point.
The all-test relative-identity condition places the chosen section's image
in the actual relative identity open. The section-identity-open criterion
then proves that its actual residue-fibre point at the chosen lift lies in
the identity component. The existing section-neighbourhood constructor
supplies its actual section-lift data on an open around that lift.

The transporter-coordinate adapter expresses the section's equation in the
canonical standard-torus coordinates on this affine etale base. Finally,
`rankOneIdentityComponentReductiveNeighbourhood_of_affineEtale` transfers
the original actual profile to the lifted point, applies the proved field
theorem `rankOneWeylReductivity`, and descends its good open to the original
base by the actual locus base-change equality and openness of the etale
map.

The provenance is internal: actual identity-component inclusion and all-test
transporter functoriality, integral automorphism base-change compatibility,
Worker 1683's geometric-field-to-etale identity-transporter construction,
the actual section neighbourhood, and the existing rank-one/open-descent
constructors. The arbitrary base may be nonreduced or nonnoetherian, and
the original ambient fibres may be disconnected. Construction of the
initial relative torus and the original forward field root/reflection
data remains part of the general openness proof.
