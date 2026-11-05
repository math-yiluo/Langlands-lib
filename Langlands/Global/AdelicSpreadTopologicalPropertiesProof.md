# Topological properties of actual adelic points from a specified spread

`adelicSpreadTopologicalProperties` proves exactly
`AdelicSpreadTopologicalPropertiesStatement` in arbitrary common universe
`u`. It covers both global-field characteristics, finite constant fields
with their original actions, every finite `S` including empty `S`,
nonaffine finite-type arithmetic models and all infinite number-field
factors.

For each specified arithmetic model `X`, field scheme `Y` and isomorphism
from the actual generic fibre of `X` to `Y`, the proof fixes the named
fixed-model and spread topologies. The existing
`curvePlaceSpreadAdelePointHomeomorph` or
`numberFieldSpreadAdelePointHomeomorph` is a homeomorphism from actual
full-adele model points to actual adelic points of `Y` with these precise
topologies.

`adelicFixedModelLocalCompactness` gives local compactness of the source,
and the forward implication of the homeomorphism's
`locallyCompactSpace_iff` transfers it to the target.
`adelicFixedModelSecondCountability` gives second countability of the
source. Applying `Homeomorph.secondCountableTopology` to the inverse
homeomorphism transfers that property to the target. Neither step
requires separation.

For the Hausdorff clause, the proof introduces exactly the target's
`IsSeparated X.hom` premise. The fixed-model local-compactness theorem
then supplies a Hausdorff source. The inverse homeomorphism embeds the
target in this source, so `Topology.IsEmbedding.t2Space` gives its
Hausdorff property. No separatedness descent, existence of a spread,
or assumed topological property is used.

This implements the property transfer accompanying the point
identification (3.5.1), Corollary 3.7 and the opening of Section 4 in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp.6 and 9. The fixed-model, nonseparated
and empty-`S` extensions are derived as explained in the unchanged
statement Markdown and the two prerequisite proofs. The present result
concerns an arbitrary specified spread; existence, model independence
and a separated-generic-fibre formulation remain separate results.

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
