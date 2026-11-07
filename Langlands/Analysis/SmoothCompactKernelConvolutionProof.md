# Smooth compact-kernel convolution proof

Authors: Worker 116 and Worker 1659. The theorem
`Langlands.Analysis.smoothCompactKernelConvolution` proves exactly the published
`Langlands.Analysis.SmoothCompactKernelConvolutionStatement`. It retains the
three independent universes of the real normed model `V`, the original Lie
group `G`, and the complete complex normed target `E`, together with the
original group operations, topology, charts, Borel measure `μ`, continuous
weight `w` and scalar kernel `κ`.

For each parameter `p`, the actual integrand
`y ↦ κ(y⁻¹*p) • w(y)` is continuous. The map `y ↦ y⁻¹*p` is a homeomorphism,
so composing `κ` with it preserves compact support. Scalar multiplication
by the continuous weight preserves this compact support. The imported
`Continuous.integrable_of_hasCompactSupport` therefore proves Bochner
integrability against the original measure, which is finite on compact sets.

For smoothness at a given `p₀`, local compactness supplies a compact
neighborhood `D`. The proof sets `K = D * (tsupport κ)⁻¹`; continuity of the
group operations makes `K` compact and hence closed and Borel. Restricting
`μ` to `K` gives a finite measure `ν`. The compact subtype `K` carries
`ν.comap Subtype.val`, and the weight is exactly `w` restricted by the
continuous inclusion `j : C(K,G)`.

The scalar kernel `k(p,y) = κ(y⁻¹*p)` is jointly real manifold smooth by the
original smooth inversion and multiplication. The published
`compactManifoldWeightedIntegral` applies to this kernel, the compact subtype
with its finite comap measure, the original parameter and integration
manifolds `G`, the inclusion `j` and the restricted weight. Its smoothness
conclusion concerns the literal integral over this fixed compact subtype.

For every `p ∈ D`, `integral_subtype_comap` converts that subtype integral
to a set integral over `K` against `ν`; restricting `μ` twice to `K` equals
restricting it once. If `κ(y⁻¹*p) ≠ 0`, then `y⁻¹*p ∈ tsupport κ` and
`y = p * (y⁻¹*p)⁻¹ ∈ K`. Thus the original integrand vanishes outside `K`,
and `setIntegral_eq_integral_of_forall_compl_eq_zero` identifies the compact
integral with the full original integral. This equality holds throughout
the neighborhood `D`. Local congruence of manifold smoothness proves the
desired conclusion at `p₀`.

This is an internal derived proof using the published manifold
weighted-integral theorem and imported Mathlib compactness, Lie-group and
Bochner integral results; it is not a transcription of an external source.
The argument requires no invariant measure, finite-dimensional model,
separability, global integrability or smoothness of `w`. It proves no
representation-orbit identity, kernel existence, concentration, density,
finite-level compatibility or automorphic tensor realization.
