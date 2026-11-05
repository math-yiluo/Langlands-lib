# Actual affine charts in projective scheme-point spaces

This module constructs the actual standard affine charts needed for the
affine-line subspace-topology assertion in Conrad (2011), printed p.10, Example 4.3. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The generic chart adapters are derived infrastructure, not separately stated
results in Conrad.

The projective affine chart uses the published homogeneous-localization
polynomial equivalence from the actual polynomial-Proj base-change proof.
Its spectrum isomorphism, followed by the published homogeneous chart
inclusion, defines the relative open immersion. Reindexing the unique remaining
coordinate for n = 1 gives the actual standard affine-line inclusion with
homogeneous coordinate convention [1:a]. Its point map evaluates the actual
relative polynomial affine-line point and postcomposes with that inclusion.

The point map is injective over every commutative coefficient algebra and
commutes with every coefficient algebra map. For a local commutative
topological coefficient ring with open units, it is an open embedding for the
independent scheme-point topology: the actual affine-line coordinate
homeomorphism is followed by the actual scheme-point map of the proved open
immersion. These local facts do not yet establish an adelic subspace comparison
or non-local-compactness. Those remain separate assertions.

`projectiveChartAlgebra` names the actual homogeneous localization;
the reused `P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv_X` proves that each remaining polynomial variable
is exactly the corresponding homogeneous coordinate ratio. Thus the line
reindexing uses the ratio X1/X0 as its unique coordinate. The open-immersion
proofs compose the actual spectrum isomorphism and the published homogeneous
chart open immersion, with their structural morphisms unchanged. This
construction includes every natural dimension and arbitrary commutative rings,
including the zero ring; its local-topology assertion has exactly the separately
listed local-ring and open-unit hypotheses.
