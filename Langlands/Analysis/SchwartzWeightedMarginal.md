# Weighted marginals of Schwartz functions

`schwartzWeightedMarginal` integrates a Schwartz function on `E × F` in its
second variable against a measurable complex weight `κ` and a measure `μ`.
It assumes that `‖κ(y)‖ (1 + ‖y‖)^(-q)` is integrable for one nonnegative
integer `q`. The result is a Schwartz function on `E`.

For each derivative order the proof restricts the ambient iterated derivative
to the directions in `E`. The inclusion into the product is an isometry.
A Schwartz seminorm of the original function bounds the restricted derivative
with decay in both variables. The assumed integrable function dominates all
derivatives of a given order in the integrated variable. Differentiation under
the integral therefore makes the averaged derivatives a Taylor series for the
marginal. Multiplying by `‖x‖^k` and integrating the same bound yields the
Schwartz estimate for every `k`.

`schwartzBoundedMarginal` applies the result to a bounded weight and a measure
of temperate growth. `schwartzSlice` uses an affine isometric inclusion to fix
the second variable. These are internal analytic tools for the triangular
matrix integral and its Fourier transform.
