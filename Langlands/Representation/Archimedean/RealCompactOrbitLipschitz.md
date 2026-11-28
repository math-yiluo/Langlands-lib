# A Lipschitz estimate for smooth orthogonal orbits

`RealCompactOrbitLipschitzStatement` applies to a jointly continuous
representation `R` of `GL_n(ℝ)` on a complex Banach space `E`. Write `ε(v)`
for the empty-word value of a genuine smooth vector `v`. Its orbit
`k ↦ R(k) ε(v)` on `O(n)` is Lipschitz for the row-sum operator norm on real
matrices. The constant is bounded by a representation-dependent factor times
the sum of the empty-word norm and the genuine first-derivative norms along
the skew projections `(Eᵢⱼ − Eⱼᵢ)/2` of the standard real matrix units. The factor is independent of the smooth
vector and of the two orthogonal points. The statement includes rank zero.

## Proof

The derived operator is real linear in its matrix direction. The skew
projection `(X − Xᵀ)/2` fixes every skew matrix. Apply it to the
standard-basis expansion of such a matrix. The resulting expansion bounds
its derivative by the direction norm times the sum of the indicated skew
derivative norms, with a fixed factor from the basis coordinate norms. Differentiating the curve `k exp(tX)` in the units
chart, for a skew direction `X`, gives the translate by `k` of that derivative.
Joint continuity supplies one operator norm bound on the whole orthogonal
subgroup.

For a given pair of orthogonal points, choose a complex bounded functional
of norm at most one taking the orbit difference to its norm. Apply the local
skew-logarithm Lipschitz estimate of `OrthogonalLocalLogarithm` to this scalar
orbit coefficient. Its supremum norm and right skew derivatives satisfy the
bounds above. The chosen functional recovers the original Banach norm of
the difference, giving the stated uniform estimate.

This is the Banach-valued consequence of the scalar skew-logarithm estimate.
It controls the error of compact averaging in the original norm when the
averaging kernels have a quantitative first moment about the identity.
Central compact averages commute with the skew derivatives appearing in the
bound, which allows the estimate to be iterated.
