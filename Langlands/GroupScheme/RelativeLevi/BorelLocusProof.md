# The Borel locus of a relative parabolic is open and closed

Workers 597 and 647.

`Langlands.GroupScheme.relativeBorelLocusClopen.{u}` proves the unchanged
`Langlands.GroupScheme.RelativeBorelLocusClopenStatement.{u}`. For every scheme
`S`, reductive group scheme `G` over `S`, and relative parabolic homomorphism
`i : P → G`, the set of points where the actual residue-field inclusion is
geometric Borel is open and closed. There are no additional hypotheses.
The theorem has an arbitrary universe parameter `u`.

The proof applies
`relativeBorelLocusClopen_of_splitMaximalTorusCharts` to
`relativeParabolicSplitMaximalTorusCharts`. The latter theorem is proved in the
supporting `SplitMaximalTorusChartProof` module: a maximal torus in a geometric
parabolic fibre gives a point of a smooth relative Hom parameter scheme.
Open restrictions make the torus maps into the parabolic and the ambient
group closed immersions and make the ambient torus geometrically
self-centralizing. Étale local sections of this smooth family provide an
affine chart above each specified base point with the required split maximal
torus on every geometric fibre.

On each such affine chart, the reduction identifies the residue-field Borel
locus with the absence of opposite nonzero weights in the actual geometric
Lie weight-rank profile. The full profile is locally constant, so the locus
and its complement are open. The arbitrary-base pullback identity for the
Borel locus and openness of étale maps then descend clopenness to `S`.
The supporting reduction and chart-proof Markdown describe these arguments
and their actual pullback comparisons in detail.

This is a composition of the proved chart construction and the proved
reduction. It does not assume the chart statement, alter the published target,
or impose affineness, connectedness or a finiteness condition on the base.
