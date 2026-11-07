# Smooth vectors from the actual integrated isometric action

`Langlands.Analysis.IntegratedIsometricSmoothVectorsStatement` concerns the
existing operator `integratedIsometricAction` and the existing submodule
`Langlands.Archimedean.smoothVectors` of the original representation.

Let `G` be a locally compact Hausdorff topological group with its Borel measurable
structure and a specified real smooth Lie-group structure modelled on a real
normed space `V`. Let `μ` be a left invariant measure finite on compact sets.
Let `E` be a complete complex normed space, and let `π` be a group homomorphism
into its bounded complex linear endomorphisms that preserves every vector norm.
Every orbit is explicitly assumed continuous and almost everywhere strongly
measurable for `μ`, as required by the original integrated-operator constructor.

For a real manifold smooth scalar kernel `κ : G → ℂ` with compact topological
support, the target first asserts integrability of the inverse kernel
`g ↦ κ(g⁻¹)`. For any proof of this integrability and any original vector `x`,
the actual constructed vector

`integratedIsometricAction(μ,π,g ↦ κ(g⁻¹))(x)`

belongs to the existing smooth-vector subspace of `π`. By that subspace's
definition, its original orbit map under `π` is real manifold smooth. The
group, model space and Banach space have three independent universes.

This is an internal consequence of the integrated-action left translation
identity and smooth compact-kernel convolution. The inverse kernel is continuous
and has compact support by the inversion homeomorphism, so compact finiteness of
the original measure proves its integrability without a measure substitution.
The left translation identity, specialized to this inverse kernel, gives

`π(p)(integratedIsometricAction(μ,π,g ↦ κ(g⁻¹))(x))`
`= ∫ y, κ(y⁻¹*p) • π(y)x ∂μ`.

The original orbit `y ↦ π(y)x` is a continuous Banach-valued function. Smooth
compact-kernel convolution therefore makes the displayed integral smooth in
`p`, which is precisely membership in the existing smooth-vector subspace.
These are proof obligations for an exact-target successor; this file states
the proposition and supplies no proof.

No right invariance, inversion invariance, unimodularity, nonzero measure,
separability, second countability or finite-dimensional model is assumed.
Almost everywhere strong measurability is retained explicitly, rather than
inferred from continuity under unstated countability assumptions.
Normalized kernel existence, concentration, smooth-vector density, finite
level comparisons and automorphic tensor realization remain separate
obligations.
