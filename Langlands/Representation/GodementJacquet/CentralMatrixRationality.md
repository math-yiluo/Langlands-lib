# Rational continuation from compact scalar covers

This internal analytic consequence combines the matrix central recurrence with
the compact-support Laurent integral. It uses the canonical p-adic topology,
normalized absolute value, shared GL Haar measure, and the existing JPSS shift.
The hypotheses explicitly require a translating matrix with absolute determinant
below one, a scalar covariance law for a continuous coefficient, and a compact
scalar cover of its support.

The central geometric denominator is the Laurent polynomial
`1 - C(omega * weight(z, shift)) * T(ord(det z))`. At the spectral point
`q^(-s)`, it evaluates exactly to `1 - omega * weight(z, s + shift)`.
The common right half-plane for the norm of the ratio shows this denominator is
nonzero. For each test and coefficient satisfying the hypotheses, the compact
central difference supplies a Laurent numerator. Haar-invariant recurrence gives
actual convergence and the quotient integral wherever the ratio has norm below
one. Laurent evaluation and regular rational division then give an actual
shifted rational continuation and its numerator clearing identity. Reduced
rational denominators are proved nonzero on that half-plane.

No supercuspidal compactness, central character, or scalar covariance existence
is asserted here. This helper does not claim cancellation of the central
geometric denominator or a functional equation.

The canonical local instances have explicit module-specific names so this helper
can be imported together with the matrix analytic-data interfaces. Their
definitions, all mathematical declarations, and all hypotheses are unchanged.
