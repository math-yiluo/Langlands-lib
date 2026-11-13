# Compact overgroups of facet fixers

This internal construction uses `KPBuildingDatum D` over a
nonarchimedean local field in arbitrary universe `u`, with the sole
geometric premise `D.SatisfiesGroupAxioms`. Rational points carry their
canonical point topology.

`map_facetZeroStabilizer_eq_facetZeroFixer` identifies the setwise
facet stabilizer, viewed inside the zero subgroup and then mapped
into the rational-point group, with the actual pointwise fixer
`facetZeroFixer D Fa`. The group axioms provide a building Tits
system and the published pointwise-fixation result for facet
stabilizers. The reverse containment follows directly from
pointwise fixation. The Tits-system facet bijection then proves
`facetZeroFixer_injective`.

`exists_facetZeroFixer_eq_of_isCompact` takes any compact subgroup
`H` contained in the zero subgroup and containing the pointwise
fixer of an actual facet `C`. It produces a facet `Fa` with
`H = facetZeroFixer D Fa` and `Fa` preceding `C`. In particular
the statement applies when `C` is a chamber, but it does not require
that restriction.

The implemented proof first uses `AvailableFixedFacet` to bound
`H` by a facet fixer. In the Tits system supplied by the group
axioms, `H` lies between two actual facet stabilizers. The lower
one is parabolic, so `H` is parabolic. The upper one is admissible;
`isAdmissibleParabolic_of_le` from `TitsAdmissibleSubparabolic`
makes `H` admissible. The existing facet bijection now gives the
required equality. Its reflected incidence property turns the
original fixer containment into `Fa` preceding `C`.

`compactOvergroupFacet` chooses this face and bundles it with the
proved equality and incidence. Together these results are internal
deductions from already proved fixed-point, pointwise-fixation and
Tits-system facts. They do not assert boundedness or compactness
of a normalizer, identify a reductive quotient with a torus, or
prove a maximal pro-p assertion.
