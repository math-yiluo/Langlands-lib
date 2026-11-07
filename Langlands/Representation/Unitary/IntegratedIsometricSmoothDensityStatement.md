# Norm density of the original action's smooth vectors

Worker 116 states
`Langlands.Analysis.IntegratedIsometricSmoothDensityStatement` with three
independent universes for the real model, group and complex vector space.
Let `G` be the original Hausdorff topological group with its real smooth
Lie-group structure modelled on a finite-dimensional real normed `V`,
its Borel measurable space, and a left invariant measure finite on compact
sets and positive on nonempty open sets. Its finite-dimensional chart model
implies local compactness; the proposition imposes no further local or
global countability assumption.

Let `E` be a complete complex normed space and `π : G →* (E →L[ℂ] E)`
the original action. Require vectorwise norm preservation, explicitly AE
strongly measurable orbit maps for the original measure, and continuity
of each orbit map on the original group. Then the existing complex
subspace `Langlands.Archimedean.smoothVectors 𝓘(ℝ,V) π` is dense in the
original norm topology of `E`. Membership in this subspace means real
manifold smoothness of the original orbit `g ↦ π(g)x`.

This is an internal consequence of the concentrating inverse-kernel
sequence, smoothness of actual integrated vectors, and the existing
strong-approximation theorem. Choose the real smooth compact kernels
before any vector, and use the nonnegative inverse weights
`f n g = κ n (g⁻¹)`. The original-measure integrals of these weights are
one and their ordinary supports eventually lie in every identity
neighborhood. The existing
`Langlands.Analysis.integratedIsometricApproximation` proves norm
convergence of the actual `integratedIsometricAction` vectors to every
original vector. Complexification of each original smooth real kernel
and `IntegratedIsometricSmoothVectorsStatement` place those vectors in
the original smooth-vector subspace. A limit of points of that subspace
lies in its closure, giving density. These are proof obligations; this
file defines the proposition only.

The construction uses left Haar translation with the inverse-kernel
convention and keeps the original representation, group, measure and
manifold structure. It needs no right or inversion invariance,
unimodularity, fixed Haar normalization, separability, global second
countability, Hilbert inner product, or finite-dimensional vector space.
It asserts no operator-norm convergence. Nonzero measure is supplied by
positivity on open sets; the model may have dimension zero.

This target is about real-manifold smooth vectors of a Lie-group action.
Finite adelic smooth vectors, their simultaneous compatibility with this
smoothing, actual automorphic quotient realizations, compact-type
finiteness, the Getz–Hahn tensor realization, admissibility, growth, decay,
compactness and spectral decomposition remain separate obligations.
