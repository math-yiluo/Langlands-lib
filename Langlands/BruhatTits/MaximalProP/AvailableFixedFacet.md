# Compact subgroups fix facets on available Bruhat–Tits data

This internal helper derives fixed-point and fixed-facet consequences from the
published Library theorems. It works at arbitrary universe `u` for a
nonarchimedean local field `F`, an affine group scheme `G`, and supplied
`D : KPBuildingDatum G` satisfying `D.SatisfiesGroupAxioms`.
For the setting of `AvailableMaximalProPStatement`, the latter hypothesis is
provided by `KPBuildingAssignment.IsAvailableFor.groupAxioms`; global
availability for other groups is not needed.

`exists_fixed_point_of_isCompact` states that every compact subgroup `H` of
`G(F)` fixes a common point in the actual reduced building of `D`. Compactness
uses the canonical rational-point topology. The proof obtains Hausdorffness
from that topology, uses
`localFieldAffineBoundedCompactness_proof` to make the compact set algebraically
bounded, and applies `boundedSubgroupFixedPoint`. All its building hypotheses
are projections of the single-group axioms.

`le_facetZeroFixer_of_fixed_point` states that if `H` is contained in
`D.base.zeroSubgroup` and fixes a point `x`, then it lies in the pointwise zero
fixer of the facet containing `x`. The containing facet is the published
`buildingFacetAt x`. Its equivariance and uniqueness show that every element
of `H` preserves this facet as a set. The published theorem
`facetZeroStabilizer_smul_eq` then gives pointwise fixation, using the Tits
system at a regular apartment point. Such a point exists by the apartment root
axioms.

`exists_le_facetZeroFixer_of_isCompact` combines the two results: every compact
subgroup of the zero subgroup lies in a facet zero fixer.
`compactSubgroupFixedFacet` chooses such a facet and bundles it with the proof
that `H` is contained in its zero fixer; it has no canonical-choice assertion.
`exists_le_facetZeroFixer_of_isProP` obtains the same conclusion for every
pro-`p` subgroup of the zero subgroup, using compactness from the existing
`Langlands.Cohomology.IsProPSubgroup` predicate. The prime is arbitrary in
this last helper.

These are derived internal consequences of the named published declarations,
not new translations of literature statements. They implement the initial
fixed-facet step in the expected proof of corrected KP Proposition 13.5.2.
They assert neither maximality of the fixed facet nor chamber containment,
the pro-`p` property of facet radicals, or any normalizer equality.
