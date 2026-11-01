# Raw convolution as an actual compact-index smooth average

Author: Worker 94.

This internal derivation specializes the actual compact-index average to a compact smooth kernel. The parameter space is the compact inverse image of the original kernel's topological support under inversion. Its inclusion is the continuous group-valued parameter map, its measure is the subtype comap of Haar measure restricted to this compact set, and its weight at `j` is the original kernel value at `j⁻¹`. Compact finiteness of Haar measure makes this subtype measure finite.

Subtype integration and repeated restriction identify the compact-domain integrals with the corresponding full group integrals, since the kernel vanishes outside the inverse support. In particular the complex integral of the weight is exactly the inverse-kernel integral. When the original kernel has nonnegative real values, its weight has norm equal to its real part. Taking real parts under the integrable scalar integral proves that the integral of the weight norm is one whenever the inverse-kernel integral is one.

For the actual smooth compact average, the scalar integral is therefore the full group integral of `κ(g⁻¹) f(xg)`. The substitution `y = xg` uses only left invariance of Haar measure and identifies this with the published pointwise raw convolution `∫ y, f(y) κ(y⁻¹x)`. Inversion invariance is neither assumed nor used. The smooth average is the previously constructed actual smooth function, so this identifies a smooth lift at every point. The module retains arbitrary number-field universe and every natural rank, including zero.

The general compact-index closed-orbit theorem puts this average in the closed span of its translations by points in the inverse support. This translation family is contained in the full group orbit, so monotonicity of span and topological closure puts the same smooth lift in the closed full group orbit span. `exists_smoothLift_mem_closed_groupOrbit` records both this membership and the exact pointwise raw-convolution formula, without a compact-finiteness hypothesis.

This is a derived helper, with provenance in the published raw-convolution definition, the actual compact-index average construction, and Mathlib's subtype integral and left-translation integral identities. It does not construct kernels, prove reproduction, or prove automorphic differential growth.
