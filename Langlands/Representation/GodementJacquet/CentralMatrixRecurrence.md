# Central differences of actual matrix integrals

This internal helper applies the contracting scalar recurrence to the actual
full-matrix integrands. Left multiplication by an invertible matrix is a
homeomorphism of the full matrix space. Pullback therefore preserves matrix
tests. The difference of a test and its inverse translate vanishes at zero;
for a coefficient supported in a compact scalar saturation, the earlier
compact-cover theorem gives compact support of its product with this
difference on GL.

If the absolute determinant of the translating matrix is below one, every
inverse orbit eventually leaves the compact support of a matrix test.
The proof bounds the continuous absolute determinant on that support and
uses growth of the inverse determinant powers. For any fixed central
scalar and complex shift, the norm of the resulting geometric ratio is
below one on a common right half-plane, independent of the test and
coefficient.

The coefficient covariance law and multiplicativity of determinant weights
give the exact integrand finite-difference identity. Assuming convergence
of this difference at a parameter where the ratio has norm below one,
Haar invariance and the orbit escape lemma apply the earlier recurrence
theorem. The result includes actual integrability of the original matrix
integrand and its integral as the difference integral divided by one minus
the ratio. Continuity of the absolute value and coefficient, scalar
covariance, and determinant contraction remain explicit premises. No
supercuspidal consequence or rational continuation is asserted in this
initial analytic helper.
