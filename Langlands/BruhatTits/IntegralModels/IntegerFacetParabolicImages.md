# Residue images of incident integer-valued building facets

This internal interface uses the original `IntegerValuationBuildingData`
over an arbitrary field `K`, with its original quotient, full facets and
common-apartment incidence relation. It requires no topology or local-field
instance on `K`. A local domain `R` with fraction field `K` is supplied.

`IntegerFacetModelData` supplies relative-component model pairs of these actual
full facets and their generic-identity morphisms in the usual opposite
incidence direction. It asserts no existence theorem. Its
`incidentParabolicImage` is the all-test range of the existing actual
schematic-image inclusion into a supplied neutral-special-fibre quotient.
`HasFacetParabolicOrderBijection` exposes the same bijection and opposite
inclusion assertion as the local-field `FacetModelData` interface. The
bijection remains a hypothesis, rather than a theorem of this unit.

Generic rigidity makes the neutral special-fibre self-comparison the identity,
without an additional coherence axiom. If the supplied quotient is an actual
reductive quotient, the self-image equals the whole quotient. Its quotient map
is scheme-surjective by its represented fppf-quotient property. Its schematic
image inclusion is therefore a surjective closed immersion into the reduced
quotient, hence an isomorphism. Its all-test range is consequently the whole
group. This proof does not assume that an fppf cover is surjective on the point
groups of every original test scheme.

These are derived constructions from `SpecialFibre`, the integer building's
incidence relation, generic rigidity, and smooth reducedness over a field.
They prepare the residue-parabolic maximality argument for the actual maximal
unramified field, where the local-field building interface cannot be used.
They construct neither models nor a facet-parabolic bijection, and do not
establish the prescribed-point split-torus theorem.
