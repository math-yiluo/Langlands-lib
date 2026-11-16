# Actual chart squares for refining a specified formal comparison

This internal module constructs `refinementChartSquare` for a
specified actual full-order formal comparison and a further
refinement of its left finer atlas.

The top map is precisely the chart evaluation of the rationalized
coordinate isomorphism of `c.refine q`. The bottom map is the
original coordinate isomorphism on the selected original finer
chart. The two vertical maps are the specified
direct-to-successive comparisons followed by the corresponding
actual refined-chart identifications. The target further
refinement is retargeted along the comparison's exact equality of
finer covers.

The proof uses the actual restriction chart square for the
original coordinate quasi-isogeny. Tensor composition identifies
the refined coordinate map with the specified left comparison,
restricted map and inverse right comparison. Cancelling that
right inverse pair and reassociating gives the commuting square.

The scalar ring is a commutative domain with specified fraction
field, the coefficient ring is any commutative scalar algebra,
and the acting order is any algebra ring. Finite coordinates may
differ, covers may be infinite, and test algebras use the
coefficient-ring universe. Every chart requires its actual
generator to be a unit on that test algebra.

The provenance is internal from actual formal comparison
refinement, its specified coordinate maps and the actual rational
restriction/composition equations. No point-evaluation
faithfulness, height or moduli-representability assumption is
used.
