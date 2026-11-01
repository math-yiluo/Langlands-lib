# Integrability from a contracting scalar recurrence

This internal analytic helper supports the central-character convergence step
of the Godement–Jacquet supercuspidal argument. It is a derived
measure-theoretic construction, not a claim that an arbitrary matrix
coefficient or test already meets its premises.

The definition `geometricDifference T r H` is the function
`x ↦ H(x) - r H(T(x))`. Finite telescoping gives its weighted partial sum
as `H(x) - r^N H(T^N(x))`. If each orbit reaches a zero of `H`, the norm of
`H(x)` is therefore bounded by the nonnegative infinite sum of the norms of
the weighted differences.

For a measure-preserving map, the lower integral of that bound is the lower
integral of the difference's norm multiplied by the geometric series with
ratio `‖r‖`. An integrable difference and `‖r‖ < 1` consequently imply
integrability of the measurable function `H`. For a measure-preserving
measurable equivalence, translation invariance of its Bochner integral then
gives the exact quotient by `1-r`. The proof explicitly establishes that this
denominator is nonzero.

The intended application uses inverse multiplication by a scalar uniformizer.
Compact support of a matrix test supplies orbit escape; support modulo the
center supplies compactness of the test's scalar finite difference. Those
geometric and representation-theoretic premises are separate obligations.
