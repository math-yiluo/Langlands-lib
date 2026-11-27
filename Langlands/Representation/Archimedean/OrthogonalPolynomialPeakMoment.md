# First moment of an orthogonal polynomial peak

`polynomialPeak B` is the function \(p(k)=1-\operatorname{distSq}(k,1)/(2B)\) on the real orthogonal group. `distSq_one_eq_trace` shows that \(p\) is affine in the matrix entries. `exists_polynomialPeak_parameter` supplies a positive \(B\) at least \(n^2\) and at least the squared distance from the identity of every orthogonal matrix.

For such \(B\) and positive rank, `OrthogonalPolynomialPeakMomentStatement` asserts that the integral of \(p^{t^4}\) is positive for every positive integer \(t\). The Haar first moment of the Frobenius distance with respect to the normalized density \(p^{t^4}\) is bounded by \(C/t\), for a constant independent of \(t\).

`orthogonalPolynomialPeakMoment` uses Bernoulli's inequality to bound \(p^{t^4}\) below by \(1/2\) on the ball of radius \(n/t^4\). The polynomial Haar lower bound for that ball bounds the normalizing mass below. For the numerator, inside the ball of radius \(n/t\) the distance is at most \(n/t\). Outside it, \(1-u\le e^{-u}\) gives \(p^{t^4}\le e^{-n^2t^2/(2B)}\). A term of the exponential series bounds this tail after division by the polynomial lower bound for the normalizing mass.
