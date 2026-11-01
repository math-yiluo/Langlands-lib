# Smooth compact coordinates of actual right-translation orbits

The helper `matrixDerivativeRightOrbitValue` also records the actual derivative
orbit with parameter and evaluation point both in ambient matrix coordinates.
`matrixDerivativeRightOrbitValue_contDiffOn` proves joint smoothness on the
product of the open units domains by the same finite adjoint expansion.

Authors: Worker 94; Worker 348 (the covariance expansion adapted from the
published continuity proof); Worker 566 (the underlying finite coefficient
induction, upgraded in the imported smooth coefficient helper).

This internal helper uses the genuine derivative topology, smooth functions
and positive right action. On the open set of invertible mixed matrices it
proves smoothness into each normed continuous-function space obtained by
restricting a genuine enveloping derivative to an arbitrary compact subset
of the completion-based group.

The proof expands `D(a) R(g) f` as the finite sum
`sum_i c_i(g^-1) * (D(b_i)f)(x*g)`. The expansion follows from published
covariance, as in Worker 348's continuity proof, with the smooth coefficients
constructed from Worker 566's algebraic argument. In ambient matrix
coordinates each summand is jointly smooth in the translating matrix and
the evaluation matrix on the product of their open unit domains.
The compact-family calculus helper then gives smoothness in the supremum
norm on every compact restriction. No manifold structure on the compact
set is required.

The normed derivative-coordinate embedding and real Hahn--Banach
scalarization give smoothness after every continuous complex linear
functional on the actual derivative topology. Pullback by the units
inclusion constructs `smoothOrbitCoefficient` as a genuine element of
`SmoothFunctions K n`. The same number-field universe and all ranks,
including zero, are retained. This helper concerns scalar smoothness;
commutation with the genuine enveloping action remains a separate step.
