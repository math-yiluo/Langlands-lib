# The complex Lie group of unramified characters

Author: Worker 559.

`Langlands.Plancherel.rationalUnramifiedComplexLieGroup` proves
`Langlands.Plancherel.RationalUnramifiedComplexLieGroupStatement.{u}`. For each
connected reductive group \(G\) over a nonarchimedean local field and each integer
basis \(b\) of its valuation image, the group \(X(G)\) of unramified characters is a
complex Lie group in the chart given by \(b\). This is the analytic Lie group part
of Renard's description of the complex torus in V.3.20. [Published statement](RationalUnramifiedComplexTorusStatement.md)

The proof uses the published open embedding of the basis coordinates into
\(\mathbb C^r\), where \(r\) is the valuation-image rank.
`IsOpenEmbedding.isManifold_singleton` gives an analytic manifold in that chart.
`contMDiff_isOpenEmbedding` makes the coordinate map analytic, and
`ContMDiff.of_comp_isOpenEmbedding` lets us prove analyticity of each group
operation after composing with the coordinate map. [Basis chart](RationalUnramifiedComplexChart.md)

The inverse of `rationalCanonicalImageUnramifiedContinuousEquiv` followed by
`rationalImageBasisUnitCoordinates` is a multiplicative equivalence to tuples of
complex units. The basis coordinates are the underlying complex values of those
units. Thus in coordinates, the product of characters is the coordinatewise
product. The proof composes the pair of coordinate maps with `contDiff_mul` on
\(\mathbb C^r\) to obtain analytic multiplication.

Inversion of characters similarly gives coordinatewise reciprocals. Each basis
coordinate is nonzero by `Units.ne_zero`. At each point of the chart image,
`ContDiffAt.inv` gives analyticity of the reciprocal of each coordinate
projection, and `contDiffAt_pi` assembles them into an analytic map at that point.
Composition with the basis coordinates proves analytic inversion.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, V.3.20, printed p. 116 (PDF p. 122). The source is registered
as `renard-2026-representations-groupes-reductifs-padiques`.
