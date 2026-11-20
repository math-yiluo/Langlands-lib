# Smooth real Godement sections for Schwartz tests

`RealGodementSchwartzSectionStatement` places the real Godement section
`sectionValue μ c f Φ` in the smooth position principal series with leading
character `c`. The lower vector `f` belongs to the position principal series
of a real block list `ds`, and `Φ` is any Schwartz function on real
`m × (m + 1)` matrices. The bound assumes that for every lower position,
`m + normExponent (realPositionExponent ds) m i ≤ Re(c.exponent) + (m + 1)/2`.
The lower measure `μ` can be any Haar measure.

The proof works in the open set of invertible upper matrices. For each lower
matrix `h`, the linear map taking the upper matrix to `h` times its trailing
rows has operator norm bounded by `‖h‖`. Each derivative of the integrand is
the corresponding Schwartz derivative composed with that map in each
argument. On a closed ball of invertible matrices, the lower-group Schwartz
estimate absorbs these additional powers of `‖h‖`. The lower Haar density
then leaves an integrable matrix decay bound for every derivative order.
Dominated differentiation and induction give smoothness. The upper
Borel covariance follows from right translation in the lower Haar integral
and the identity between the two normalized inducing characters.

This is an internal analytic step for the real Godement construction in
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, pp. 47–48.
The section uses the same determinant weights as the compactly supported
construction.
