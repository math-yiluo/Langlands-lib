# Chamber radical preimages containing pro-p subgroups

This internal construction concerns a supplied `KPBuildingDatum D` over an arbitrary-universe
nonarchimedean local field. It assumes the single-group axioms, the three explicit
`FacetReductiveComparisons D`, and `FiniteFieldSylowBorelStatement` in the same universe.
It does not prove either structural input.

For a pro-p subgroup contained in a facet's zero fixer, the neutral-points axiom places it
in the actual neutral integral-point image. The continuous actual parahoric reduction
sends it to an abstract p-subgroup. Mathlib's maximal p-subgroup existence theorem extends
this image to a Sylow subgroup, without requiring a separate finiteness hypothesis for the
point group. The finite-field input identifies that Sylow subgroup with the rational-point
image of the unipotent radical of a field-defined geometric Borel.

The facet-parabolic correspondence realizes that Borel's full subgroup functor by an
incident facet. Representability gives an isomorphism between the Borel and the actual
reductive image of the incident model morphism, commuting with their embeddings in the
quotient. Transport of the Borel condition over the field and its algebraic closure shows
that this incident facet is a chamber by the second comparison. Transport of the radical
through the same isomorphism and the third comparison identify its actual reduction
preimage with that chamber's positive subgroup. Taking inverse images gives containment
of the original subgroup.

For any pro-p subgroup of the zero subgroup, its compactness and the published
fixed-facet theorem supply the starting facet. The definition
`proPSubgroupContainingChamber` chooses a chamber together with its chamber property and
the containment in its actual positive subgroup.

This is a derived adapter using the published fixed-facet, reduction, representability,
Borel transport and radical transport constructions. It proves no maximality or normalizer
statement, and does not assert the radical preimages are pro-p. Those remain separate
obligations in the corrected KP Proposition 13.5.2 task.
