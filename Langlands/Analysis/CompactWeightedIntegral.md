# Bounded integration of scalar kernels against a continuous vector-valued weight

For a compact topological space `X` with its Borel measurable structure, a
finite measure `μ`, and a fixed continuous map `w : C(X, E)` into a complete
complex normed space, `compactWeightedIntegral μ w` is the complex continuous
linear map

`C(X, ℂ) →L[ℂ] E`, sending `f` to `∫ x, f x • w x ∂μ`.

The scalar-kernel space has its existing supremum norm. Every integrand is
Bochner integrable: it is continuous on a compact space and the measure is
finite. The estimate `‖f x‖ ≤ ‖f‖` and the norm bound for the Bochner integral
give

`‖compactWeightedIntegral μ w‖ ≤ ∫ x, ‖w x‖ ∂μ`.

The auxiliary linear map, its pointwise estimate, and the application identity
record this actual integral construction. The measure may be zero and the
compact space may be empty. The space `E` need not be finite-dimensional,
Hilbert, or separable; the two carrier universes are independent. No
smoothness is required of `w`, and no group action or invariant measure is
assumed.

Provenance is internal. The construction combines the existing norm on
compact continuous functions, compact-support integrability, linearity of
Bochner integration, and its norm estimate from the imported Mathlib
modules. It is intended to integrate scalar parameter kernels against
continuous representation orbits. Smooth dependence on parameters is a
separate proposition; this construction does not prove smooth vectors,
density, an automorphic realization, or any spectral conclusion.
