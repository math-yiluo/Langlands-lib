# Actual smooth weighted compact averages

Author: Worker 94.

This internal construction uses the published actual standard compact
subgroup and genuine matrix smooth functions, for every number field in
arbitrary universe and every natural rank, including zero. It allows
every compatible Borel structure, every finite measure, and every
continuous complex weight.

`CompactWeightedAverage.rightMultiplicationMap` is right multiplication
by the coordinate matrix of a compact element, viewed as a real
continuous linear endomorphism of the matrix space. The family depends
continuously on the compact element and preserves invertibility.

`average` is the scalar integral `∫ k, w(k) f(x k) dν(k)`.
`ambientAverage` expresses it in matrix coordinates.
`ambientAverage_contDiffOn_hasFDerivAt` applies the published
`Langlands.Analysis.compactLinearParameterIntegral` on the open set of
invertible matrices. It proves actual smoothness of this extension on
that open set and identifies its first Fréchet derivative with the
integral of the genuine partial derivatives. This does not require a
vector integral in the smooth-function space.

`average_mem_smoothFunctions` restricts the extension through the units
chart. `averageSmoothLM` proves complex linearity using integrability
of continuous scalar functions on the compact subgroup.
`averageLM` transports the resulting linear map to the derivative
topology carrier and has the exact pointwise formula `eval_averageLM`.

`ambientDerivative_integrable` obtains integrability of the continuous
family of partial derivatives from compactness. The theorem
`smoothDifferential_average` evaluates the Fréchet derivative integral
in the actual direction `g X`. The ambient extension characterization
and chain rule identify the integrand with the genuine real Lie
derivative of each right translate.

These are internally derived constructions motivated by the character
integral on printed/PDF page 8 of the registered original
`harish-chandra-1966-discrete-series-ii`. They do not yet prove continuity
in the full enveloping derivative topology or closed compact-orbit
containment. Those obligations remain necessary for
`CompactWeightedAverageStatement`; no projector, finite multiplicity,
reproduction or automorphic growth theorem is claimed here.
