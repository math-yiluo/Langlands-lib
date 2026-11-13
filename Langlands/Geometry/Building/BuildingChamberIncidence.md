# Chambers and facet incidence in the actual valuation quotient

This internal construction concerns the original `BuildingFacet B` values of
one supplied `ValuationBuildingData B`, at arbitrary universe `u`. Under
`B.SatisfiesApartmentAxioms`, `incidentChamber` chooses a chamber `Cc` for
each facet `Fc`, with the original relation `FacetPrecedes B Fc Cc`.
The companion equality theorem says that a facet above a chamber is that
chamber. Consequently two incident chambers coincide.

The affine equality lemma needs no root-system axioms. A defining point
of the lower chamber has nonzero value under every root. Membership in the
upper facet's closure therefore gives equality of signs, since the
zero-sign alternative is impossible. The defining points lie in the same
facet, giving equality of the two facets.

The affine existence lemma uses the published
`IsLocallyFiniteReflectionArrangement.exists_regularPoint_closure`.
A defining point of the given facet lies in the closure of a regular
point's facet. The existing closure formula then puts the whole given
facet in that closure, so it is a face of a chamber.

For the quotient, `isChamber_translatedApartmentMap_image_iff` reflects
chamberhood for a set already known to be an affine facet. Choose a point
shared by its image and the chamber chart. The actual quotient relation
provides a normalizer element carrying that chamber point to the chosen
coordinates. The two resulting affine facets share a point and hence are
equal. The normalizer preserves the affine roots under the apartment
axioms, so it also preserves chamberhood. This argument does not require
an extra injectivity or normalizer-stabilizer hypothesis.

The equality theorem applies that reflection lemma in the common chart
from `FacetPrecedes`, then uses the affine equality lemma. The existence
theorem applies affine chamber existence to any chart of the given
building facet and uses the same chart for the new chamber. Finally,
`incidentChamber` makes a classical choice of that proved witness and
retains both proofs in its subtype.

The provenance is internal: these are deductions from the published
affine sign definitions, regular-point closure, facet partition and
normalizer coordinate transport. This pair introduces no new
interpretation of the literature. It supplies incidence consequences used
in the corrected maximal pro-`p` argument; it does not assert a finite
reductive quotient comparison or a maximal pro-`p` conclusion.
