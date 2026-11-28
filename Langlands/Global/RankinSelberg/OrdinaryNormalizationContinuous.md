# Continuous evaluations of entire linear integral normalizations

`OrdinaryNormalizationContinuousStatement` starts with a linear family of complex integrands whose pointwise evaluations are continuous on a sequential barrelled space. Suppose all integrals converge absolutely and are holomorphic on a common right half-plane, and each integral has an entire normalization by a fixed factor. Then the normalized values form an entire linear family, and evaluation at each spectral point is continuous in the vector.

Uniqueness gives linearity of the normalizations. The identity theorem identifies every normalized function with the raw integral times the reciprocal factor throughout the common right half-plane. The integrated linear kernel is continuous there by `integrableLinearKernelContinuity`. The barrelled-space Taylor argument in `continuous_eval_of_entire` then gives continuity at every spectral point.

This is an internal continuity criterion for the scalar evaluations used in the smooth local integral families of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.3, pp. 8–9. [Author-posted edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
