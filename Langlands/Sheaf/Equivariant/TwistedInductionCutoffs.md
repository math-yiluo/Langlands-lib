# Open-subgroup invariant coordinate maps on twisted induction

This module is an internal consequence of the actual right Kan extension
coordinates in `TwistedInductionSmoothCoordinates` and the existing definition
of a locally discrete section. It retains independent universes for the category,
group and coefficient modules.

`indexedMapApp` applies a natural coefficient transformation separately at each
group coordinate. The transformations may depend on the group element.
`map_indexedMapApp` computes restriction along an arbitrary twisted arrow: the
family of transformations shifts by right multiplication by the inverse twist.

If the family is invariant under right multiplication by an open subgroup,
`isDiscreteSection_indexedMapApp` proves that it preserves discrete sections for
every lifted local action. The fixing subgroup is intersected with the subgroup
of invariance. For a general arrow in the discrete sieve, its twist conjugates
that subgroup. Conjugation preserves openness in a topological group, so the
same argument applies to every witness in the original sieve.

Consequently `discreteSieve_le_indexedMapApp` and
`indexedMapApp_mem_smoothSubmodule` preserve the existing locally discrete part.
This is a tool for stable spatial cutoffs. It neither asserts that the
group-dependent map is a natural transformation on the full twisted category
nor proves compact acyclicity.
