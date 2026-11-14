# Incident facets for prescribed residue-torus cocharacters

This internal supporting unit applies the prescribed short-ray construction
to the actual torus of an integral model. The base is a local domain `R`
with fraction field `K`; `B` is integer-valued building data for an affine
group over `K`, and `A` is `IntegralSplitTorusData N B.i` for an actual
integral model `N`. Both fields and rings have arbitrary universe `u`.
There is no smoothness or algebraic-closedness premise for this unit.

`exists_pos_incidentFacet_of_specialFibreCocharacter` lifts an arbitrary
cocharacter `nu` of `A.specialFibreTorus` through the inverse of the actual
`cocharacterSpecialization` equivalence. The imported geometry constructs
a short positive ray from any apartment point `x`. The facet of `x` is
a face of the facet entered by that ray. For an ordinary affine root
vanishing at `x` whose derivative is the root form of a relative root `a` of the generic fibre, its sign on the new point is the sign of the actual residue
integer pairing of `A.characterSpecialization a` with `nu`, viewed in
the reals. Every relative root of the generic fibre with nonnegative residue pairing
has the same nonstrict fixer on the old and new facets. Pairing
preservation under specialization gives both conclusions, including
zero pairings; no generic-cocharacter hypothesis is required.

`HasSpecialFibreCocharacterIncidentFacets` records the resulting incident
facet existence and nonnegative-root fixer equalities for every point
and every actual residue cocharacter. The separate theorem
`hasSpecialFibreCocharacterIncidentFacets` proves this proposition.

The provenance is the imported actual integral-torus specialization and
pairing identity, combined with `IncidentCocharacterFacet`. No new
external literature claim is made. This result constructs apartment
facets and compares root fixers of the generic fibre. It does not assert equality
of special-fibre schematic images with dynamic parabolics, attainment
of all parabolic subgroup functors, or the host's descended parabolic
order bijection.
