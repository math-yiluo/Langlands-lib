# Joint open-cell comparison for complex Schwartz Godement tests

`complexGodementSchwartzOpenCell` proves absolute integrability for the joint open-cell kernel and evaluates the open-cell integral of a Godement section by the partial Fourier formula. The inducing parameters are strictly dominant, and the adjoining exponent satisfies a sufficient bound from standard-module Godement convergence for the smaller list of absolute characters.

The proof uses the right-unitary-invariant Schwartz majorant of the rectangular test. With the smaller spherical majorant and the absolute adjoining character, it gives a nonnegative Godement kernel whose fibers are integrable. The corresponding larger section is constant on the unitary group. Its upper-Borel transformation law and Iwasawa decomposition identify it with a scalar multiple of the larger spherical majorant, so the strict-chamber open-cell bound applies. The determinant factor is constant and nonzero along the open-cell integration. Thus integrating the norm of a fiber gives the norm of the larger section up to that factor, and the product integrability criterion applies.

The original joint kernel is bounded by a constant times the positive majorant kernel because the additive character has norm one and the smaller vector is bounded by its spherical majorant. The established open-cell change of variables and Fubini identity then give the displayed formula.

This extends the Library's compact full-row-rank chamber comparison to arbitrary Schwartz tests on the stated half-plane. [Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 7.2 and equation (7.6)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
