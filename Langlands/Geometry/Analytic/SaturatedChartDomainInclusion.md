# Chart-domain inclusions into original compatible presentations

A chart of the saturation is a represented local domain of an original
affinoid atlas. `saturatedChartDomain` takes the corresponding literal
subspace with its contained-chart atlas. Its greatest chart retains the
full algebra of the chosen local-domain representative.

`saturatedChartDomainInclusion` composes the inclusion into the saturated
space with the same-space comparison to the original atlas. Both maps
have compatible bounded pullbacks by source saturation. On points the
composite sends a point of the chart domain to its ambient point.

At the original parent of the chosen representative,
`saturatedChartDomainInclusion_pullback` identifies the complete bounded
pullback from the parent algebra to the greatest source chart with the
representative's structural map. The first leg has the identity
restriction on that chart. For the second leg the defining equation of
the local-domain inclusion reduces to the structural map, since the
target is the whole parent chart.

This comparison follows from `SaturatedComparisonEquivalence` and
`AnalyticDomainSpaces`. It uses the enlargement of atlases by represented
affinoid domains in V. G. Berkovich, *Étale cohomology for non-Archimedean
analytic spaces*, Publ. Math. IHÉS 78 (1993), Proposition 1.2.6,
printed pp. 17–18, and compatible chart maps in Definition 1.2.7.
