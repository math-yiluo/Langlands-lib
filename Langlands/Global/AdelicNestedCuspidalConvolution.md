# Transported convolution on nested cuspidal classes

For standard \(Q\le P\), `adelicParabolicConstantTermGrowth`
sends a moderate continuous function on the \(P\)-quotient to one on
the \(Q\)-quotient. The input is invariant under \(Q(F)\) because
\(Q(F)\) maps into the subgroup defining the \(P\)-quotient. Compact
constant-term covariance gives continuity and the required left
invariance after averaging. For the growth bound, each class in the
compact radical quotient has a representative with bounded adelic
height. Rational invariance allows these representatives in the
integrand, and submultiplicativity and the probability normalization
preserve a polynomial growth bound.

`parameterConvolutionKernel` multiplies the original kernel at \(t\)
by the ratio of the \(P\)-height powers at \(gt\) and \(g\), for a fixed
external argument \(g\). For norm-one points of the smaller Levi the
two height powers are unchanged upon left translation by the Levi
point. Therefore `leviPairing_twistedConvolutionEnd` uses this
continuous compactly supported kernel directly on the untwisted
input. The integrable bounds for actual cusp tests, at a maximal
infinite Levi compact, justify the exchange of integrals. In
particular, `cuspidalQuotient_twistedConvolutionEnd_eq_of_eq` proves
that two moderate continuous functions with the same cuspidal class
still give the same class after transported convolution.

This is the compatibility of convolution and the norm-one tests
required in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §6.2, (6.8), pp. 201–202, (8.1), pp. 221–222, and
Lemma 8.3, p. 223. The operator on the cuspidal classes is the one
used in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series*, I.4.5, printed pp. 60–62
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`,
and `moeglin-waldspurger-1995-spectral-decomposition`, collection
fingerprint `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
