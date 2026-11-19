# Complex Tate zeta integrals

This internal module writes the complex archimedean zeta integral of
`ComplexArchimedeanTateStatement` in the shifted variable `u = s + t`.
It uses the target measure, twice Lebesgue area, and extends the integrand
by zero at the origin. The angular character is the integer power of
`z / ‖z‖`.

The angular factor has norm one away from the origin. On the unit ball,
the Schwartz function is bounded and the remaining real power has
exponent `2 * u.re - 2`, which is integrable in real dimension two
when `u.re > 0`. Outside the unit ball the power is bounded by a
nonnegative integer power, and the Schwartz seminorms give integrability.

The proof of holomorphy differentiates under the integral. For a parameter
`u` in the half-plane, take `δ = u.re / 2` and let the varying parameter
range over the ball of radius `δ / 2` around `u`. The derivative multiplies
the integrand by `2 log ‖z‖`. Above radius one, `log ‖z‖` is bounded by
`‖z‖^δ / δ`. Below radius one, the same bound at the reciprocal radius
controls `|log ‖z‖|`. These inequalities dominate the derivative by
`2 / δ` times the sum of the norms of the integrands at `u + δ` and
`u - δ`, both in the convergence half-plane.
