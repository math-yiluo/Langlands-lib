# Actual norm-kernel compactness through a compact central quotient

This internal derived result combines the published openness of the actual
rational common norm kernel, its published compact intersection with the full
abstract center, and `OpenHomCompactness`.

For a connected reductive group scheme over a nonarchimedean local field,
`NormKernelCompactnessThroughCentralQuotientStatement` is the Prop-valued
definition of the following conditional compactness assertion.
`isCompact_rationalCommonNormKernel_of_open_central_quotient` proves that the
actual common norm kernel is compact if an open continuous homomorphism from
the full rational-point group to a compact Hausdorff topological group has
central kernel. The source has exactly the canonical topology
`rationalPointTopology F G.X`, installed explicitly in the conclusion.
The target may be at a separate universe. Surjectivity is not required.
The named proposition and its proof explicitly bind `IsTopologicalGroup T`,
`T2Space T`, and `CompactSpace T`.

The homomorphism's kernel is closed by continuity and Hausdorffness of the
target. Since it is central, its intersection with the common norm kernel is
a closed subset of the already compact intersection of that norm kernel with
the full center. The norm kernel is an open subgroup. The imported topological
reduction therefore proves its compactness.

This is a conditional reduction. It constructs no algebraic quotient, and it
does not assert that the supplied centralizer-zero subgroup is open or compact.
The centralizer application still needs an actual quotient with all the listed
properties and the structural hypotheses of the connected reductive source.
