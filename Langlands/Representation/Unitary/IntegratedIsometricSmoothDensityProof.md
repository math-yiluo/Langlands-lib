# Density of smooth vectors by integrated approximation

`Langlands.Analysis.integratedIsometricSmoothDensity` proves
`Langlands.Analysis.IntegratedIsometricSmoothDensityStatement` with independent
universes for the real chart model, the Lie group, and the complex
representation space. The proof uses the given action, manifold structure, and
left invariant measure. [Statement](IntegratedIsometricSmoothDensityStatement.md)

`ChartedSpace.locallyCompactSpace` gives local compactness from the charts over
the finite-dimensional real model. `smoothInverseKernelSequence` gives real
smooth compactly supported kernels \(\kappa_n\). The inverse weights
\(f_n(g) = \kappa_n(g^{-1})\) are integrable and nonnegative, with integral one.
Their ordinary supports eventually lie in each identity neighborhood because
ordinary support is contained in topological support.
[Inverse-kernel sequence](../../Analysis/SmoothInverseKernelSequenceProof.md)

`integratedIsometricApproximation` uses the same sequence of weights for every
vector \(x\). The given almost-everywhere strong measurability of each orbit
and its continuity at the identity yield norm convergence of the integrated
vectors to \(x\).
[Integrated approximation](IntegratedIsometricApproximationProof.md)

The inclusion \(\mathbb R \to \mathbb C\) is smooth and preserves zero, so
composing it with \(\kappa_n\) preserves smoothness and compact support.
`integratedIsometricSmoothVectors` applied to that complex-valued kernel puts
the same integrated vector in the original smooth-vector subspace. Both
theorems use the weight \(g \mapsto (f_n(g) : \mathbb C)\).
`mem_closure_of_tendsto` then puts \(x\) in the closure of the subspace.
[Smoothness of integrated vectors](IntegratedIsometricSmoothVectorsProof.md)

This proof implements the composition of the three Library results described
in the statement companion.
