# Fixed-parameter convergence and duality of the complex Jacquet recursion

Fix the additive character, the inducing character, the larger group variable, and a
Schwartz function on the rectangular matrix space. The smaller coefficient is continuous,
has the required left-unipotent covariance, and satisfies `HasSimpleRootLogBound`.
`ComplexJacquetRecursionFixedParameterStatement` gives absolute integrability of the group
kernel for every compatible choice of Haar measures, equality with the quotient recursion,
and duality of the quotient recursion. The group kernel is (7.7) of Jacquet (2009) with
`k = h⁻¹`. The quotient recursion is (7.8).

The norm of the inducing character is the normalized determinant modulus to the real part
of its exponent. The extra determinant power and the density of matrix Haar measure
combine with it into one real exponent. Unit modulus of the unipotent character gives
the invariant norm needed in the logarithmic Iwasawa estimate. That estimate absorbs
the determinant weight and leaves polynomial powers in the norms of the inverse matrix
and last row. The partial Fourier transform of the translated Schwartz function
dominates both powers and leaves an arbitrarily high inverse power of one plus the
inverse matrix norm.

The proof inverts the group variable and extends the resulting kernel by zero to the
additive matrix space. An inverse power of the additive norm is integrable for
sufficiently high order by temperate growth of additive Haar measure. Determinant
density gives integrability on the invertible locus. Invariance under inversion and
uniqueness up to scale transfer the estimate to the supplied group Haar measure.
`complexJacquetRecursion_eq_group_of_simpleRootLogBound` then applies the Weil comparison
to obtain the equality of (7.7) and (7.8).

The quotient duality `complexJacquetRecursion_dual` applies Lemma 7.1 to the translated
rectangular test and changes variables by the smaller Weyl inverse transpose. The two
Weyl determinants give the factor `d.character (-1) ^ (r+1)` of Proposition 7.3, where
the smaller rank is `r+1`.

This internal result supplies the fixed-parameter integral step of the induction. The
identification of general standard-module Whittaker vectors with recursive kernels,
parameter dependence of those vectors, and the equal-rank functional equation remain
separate obligations.
