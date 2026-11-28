# Continuous evaluations of entire linear integral normalizations

`OrdinaryNormalizationContinuousStatement` starts with a linear family of complex integrands whose pointwise evaluations are continuous on a sequential barrelled space. Suppose all integrals converge absolutely and are holomorphic on a common right half-plane. Fix an entire denominator `D` that is nonzero throughout some right half-plane. Each integral agrees sufficiently far to the right with an entire normalization times `1/D`, with the agreement threshold allowed to depend on the vector. Then the normalized values form an entire linear family, and evaluation at each spectral point is continuous in the vector.

Uniqueness gives linearity of the normalizations. The identity theorem identifies every normalized function with `D(s)` times the raw integral throughout the common convergence and holomorphy half-plane. The integrated linear kernel is continuous there by `integrableLinearKernelContinuity`. The barrelled-space Taylor argument in `continuous_eval_of_entire` then gives continuity at every spectral point.

This is an internal continuity criterion for the scalar evaluations used in the smooth local integral families of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.3, pp. 8–9. [Author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
