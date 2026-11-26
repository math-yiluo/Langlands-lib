# Entire real normalizations from overlapping half-planes

`RealOverlappingNormalizationStatement` upgrades a
`RealJacquet.ContinuationPackage` to an entire normalized pair when the
ordinary and dual integral functions are holomorphic on right half-planes
with thresholds \(a,b\) satisfying \(a+b<1\). It takes the two reciprocal
entire denominators, a nonzero sign, and an entire, nowhere-zero epsilon
factor.

The candidate normalized function on the right is \(D(s) Z(s)\). On the
left it is
\[
\frac{D^\vee(1-s) Z^\vee(1-s)}{\mathrm{sign}\, E(s)}.
\]
The meromorphic identity theorem compares the supplied continuations with
the convergent functions in punctured neighborhoods on the two
half-planes. In their overlap, clearing the denominators at regular
arguments in the multiplied-out functional equation identifies the two
candidate values. Continuity gives agreement at each spectral point of
the overlap. The half-planes cover the plane, so the two candidates give
one entire \(N\). Reflection and multiplication by the sign and epsilon
factor give the entire dual normalization and the normalized functional
equation pointwise.

This implements the analytic gluing used for imaginary inducing
parameters in H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
Proposition 11.1, author p. 82. The convergence inputs for that application
are Lemmas 5.3 and 5.4, author pp. 36–37. Here the half-plane holomorphy and the
meromorphic continuation package are hypotheses.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
