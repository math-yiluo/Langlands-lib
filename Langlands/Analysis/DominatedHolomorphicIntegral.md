# A locally dominated integral of holomorphic functions

`DominatedHolomorphicIntegralStatement` concerns a complex-valued integrand with a finite-dimensional complex parameter space and an arbitrary measure space. Each parameter slice is almost everywhere strongly measurable. Almost every integrand is complex differentiable in the parameter on the supplied set. For each point of that set, the hypothesis supplies a ball of radius `2 * R` contained in the set and one integrable real function bounding the integrand norm almost everywhere throughout that ball. The conclusion gives absolute integrability at every parameter in the set and complex differentiability of the integral there.

At a point of the concentric ball of radius `R`, an affine complex line in a nonzero direction `v` maps the closed disk of radius `R / ‖v‖` into the larger ball. Cauchy's estimate bounds the line derivative by `B * ‖v‖ / R`, where `B` bounds the scalar function on the disk. Dividing by the direction norm gives the operator norm bound `B / R` for the Fréchet derivative.

For each basis direction, the derivative is almost everywhere the limit of the measurable slopes along that complex line. The finite basis reconstructs the Fréchet derivative as a sum of those directional derivatives times the continuous coordinate functionals. This gives the almost everywhere strong measurability required by Mathlib's dominated parameter differentiation theorem. The Cauchy bound supplies the integrable derivative bound on the smaller ball, and the original bound gives integrability at its center.

This is internal analytic infrastructure for parameter-dependent Godement integrals. It derives an integrable derivative bound from a local bound on the scalar integrands using Mathlib's complex Cauchy estimate.
