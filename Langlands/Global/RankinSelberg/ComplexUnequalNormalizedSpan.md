# Linear spanning for the normalized unequal-rank equation

Fix the smaller function and all of the inducing data. `complexUnequalNormalizedSpace` is the submodule of larger functions whose ordinary and dual kernels are integrable on a right half-plane and whose local integrals have the specified entire normalizations. The submodule is the preimage of `normalizedKernelPairs` under the paired kernel map in the larger function.

`complexUnequalNormalizedSpan` identifies submodule membership with the convergence and normalization conditions for the exact local integrals. It uses Fubini under absolute convergence to replace the joint dual integral with the iterated dual integral. In the reverse direction the maximum of the two convergence and normalization thresholds supplies a common half-plane.

This lets the adjacent-rank argument pass from test generators to their algebraic span. [Jacquet, *Archimedean Rankin–Selberg integrals*, Section 8.3](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

The same linear construction gives `complexUnequalNormalizedGrowthSpace` when both entire witnesses must have exponential strip growth. Addition and scalar multiplication of the witnesses preserve this condition. The kernel integrability and the dual Fubini identity identify membership with the growth condition for the actual pair of local integrals.
