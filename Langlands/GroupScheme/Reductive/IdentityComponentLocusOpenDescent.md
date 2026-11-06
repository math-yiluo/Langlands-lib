# Open descent for the actual reductive identity-component locus

This internal module supplies topological reductions for the existing actual
reductive geometric identity-component locus. Throughout, the ambient group
scheme is smooth and affine over its base. The base schemes and universe are
arbitrary, and the fibres may be disconnected.

An open subset of a changed base on which all geometric identity components
are reductive has an open image whenever the base map is open. The previously
proved exact base-change equality for the locus shows that this image is
contained in the original locus. It contains the image of every specified
point of the good open subset.
`IdentityComponentReductiveOpenNeighbourhood` records an actual open
subset of the original base containing the specified point and lying in
the locus. `identityComponentReductiveOpenNeighbourhood_of_openMap`
constructs these data, taking that open subset to be precisely the image
of the supplied good open subset under the open map.

Consequently, to prove openness of the locus it suffices to construct such
neighbourhoods above each point in the original locus, using open base maps.
An explicit specialization permits affine etale base changes, since etale
maps are open. Another consequence descends openness along a surjective
open morphism.

Finally, `identityComponentReductiveLocusOpen_of_affine` reduces the exact
arbitrary-scheme openness proposition to its case over all spectra of
commutative rings. The implemented proof takes the scheme's affine open
cover, applies the supplied affine theorem to the actual pulled-back group,
and uses the open-map neighbourhood result to descend the conclusion.

The provenance is internal: all proofs use the actual locus base-change
equality and standard topology of open maps, together with the existing
affine open cover. The affine theorem and the pointwise good-neighbourhood
constructions are explicit premises of these reductions. This module does
not prove them and does not supply an unconditional proof of the openness
proposition.
