# Topological laws for a quotient chart system over an affinoid atlas

`AffinoidChartSystem.AtlasProjection.TopologyStatement` states that for every
`AtlasProjection P` the charts of the actual quotient `C.Space` are embeddings,
the quotient is locally Hausdorff, and the corresponding chart ranges form
a net.

The original atlas is locally Hausdorff by its definition. The statement
requires no global Hausdorffness of either space and no nonemptiness of an
index type or spectrum. The two fields and the base and index types have
independent universes. The given projection need not be surjective. Its
chart-range inverse-image identity is part of `AtlasProjection`; the quotient
topology, embedding, local Hausdorffness, and net laws are not assumed.

This is a derived topological prerequisite for the chart gluing in Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), §1.4, printed
page 30 (PDF page 27). The original atlas and net conventions are those of
§1.2, printed pages 16–18 (PDF pages 13–15). The precise generic statement
is internal to the Library and is not asserted to occur verbatim in that
source. This pair states the laws; it supplies no proof.

The result concerns only the topology of chart gluing. The affinoid-domain
preservation and scalar-extension algebra constructions remain separate
prerequisites. Descent through quasi-isomorphisms, towers, fiber products, and
comparison with algebraic analytification remain outside this statement.
