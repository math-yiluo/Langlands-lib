# Chambers representing maximal open pro-p subgroups

This internal adapter concerns the actual positive subgroups of a supplied
`KPBuildingDatum D` over a nonarchimedean local field in arbitrary universe
`u`. It retains each structural theorem input explicitly and does not
prove those inputs or the full available-data proposition.

`exists_chamber_of_isMaximalOpenProP` assumes the single-group axioms,
`FacetReductiveComparisons D`, `FiniteFieldSylowBorelStatement` and
`LocalFieldPositiveProPStatement`. Chamber domination places a given
maximal open pro-p subgroup `H` inside the actual positive subgroup of a
chamber. The latter subgroup is contained in the zero subgroup by the
model axiom, open by the proved facet topology theorem, and pro-p by the
explicit local-model input. The maximality clause for `H` therefore makes
the containment an equality. This proves the classification direction
without presupposing that every chamber positive subgroup is maximal.

`eq_of_facetPositiveSubgroup_eq_of_isMaximalOpenProP` additionally uses the
explicit finite normal-Sylow torus and bounded-open-normalizer inputs,
without requiring the finite Sylow/Borel input. Equal positive subgroups,
one of which is maximal, have equal zero normalizers. The conditional
normalizer theorem identifies these normalizers with the respective
actual facet zero fixers. Injectivity of these fixers under the group
axioms identifies the facets. Applying this to the preceding existence
result gives `existsUnique_chamber_of_isMaximalOpenProP`.

`maximalOpenProPChamber` chooses a chamber representing `H`. Its subtype
property retains the chamber condition, equality with the actual positive
subgroup, and the equality between the normalizer of `H` intersected with
the zero subgroup and the actual fixer of that chamber.

The provenance is internal composition of the named Library interfaces:
chamber domination, the explicit local-model pro-p adapter, actual facet
topology and inclusions, the conditional normalizer theorem and fixer
injectivity. The five structural inputs needed by the strongest result
are the facet comparisons and the four stated global propositions.
Forward chamber maximality remains a separate obligation.
