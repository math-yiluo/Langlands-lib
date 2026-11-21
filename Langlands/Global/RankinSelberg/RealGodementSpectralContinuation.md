# Uniform real Jacquet continuation in positive rank

`RealGodementSpectralContinuationStatement` gives the real Jacquet family for fixed K-finite compact profiles and every inducing exponent vector in positive rank. It agrees with the open-cell integral on the strict dominant chamber. Every iterated right derivative is a regular Whittaker function and is holomorphic in the parameters at a fixed group element. Near each parameter a common polynomial growth exponent works for all those derivatives.

In rank one the upper unipotent group is trivial and its empty entry-product Haar measure has mass one. The section therefore equals its Jacquet integral. The section is the rank-one determinant character times its value at the identity. A right derivative in a \(1\times1\) matrix direction multiplies the character by the sole matrix entry times the inducing exponent. Iterating multiplies it by a polynomial in the exponent. That polynomial is bounded on each compact spectral ball, and a single determinant estimate on the ball bounds the character by a power of the matrix height. This proves the rank-one holomorphy and derivative growth.

For each higher rank the determinant Haar measure and the prescribed upper-entry Haar measure admit a compatible quotient measure by the closed subgroup quotient integration theorem. The real Godement rank step with that measure completes the induction. The normalization on the strict chamber specifies the resulting family independently of the choices in the finite frames.

The proof implements the real character continuation in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, with the locally uniform estimates for all right derivatives used by the column construction.
