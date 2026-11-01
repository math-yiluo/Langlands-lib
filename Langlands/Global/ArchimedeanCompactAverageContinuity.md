# Continuity of actual weighted compact averaging

Author: Worker 94.

This internal development proves continuity of the actual scalar compact
average in the full derivative compact-open topology. It uses the
previously constructed smooth average and its finite simultaneous
derivative expansions.

`scalarIntegralCLM` is the continuous complex linear integral on
continuous functions on the compact subgroup. Its operator bound comes
from the finite total measure. The map `weightedEvaluation` takes a
continuous function and a base point to its weighted continuous compact
orbit. Joint continuity of evaluation, followed by the compact-open
currying theorem, proves continuity into this Banach space.

`continuousAverageCLM` composes this continuous family with scalar
integration and curries again. It is a continuous complex linear map on
continuous functions with the compact-open topology.

For each genuine enveloping derivative, `derivativeExpansion` expresses
the derivative of the actual smooth average as a finite sum of these
continuous scalar averages applied to fixed derivative coordinates.
The induced definition of the derivative topology therefore gives
`continuous_averageLM` and the actual continuous operator `averageCLM`,
with the exact scalar integral formula `eval_averageCLM`.

The argument does not require completeness of the smooth-function
space or a vector integral there. Closed compact-orbit containment
remains a separate obligation. No compact projector, admissibility,
reproduction or automorphic growth is asserted.
