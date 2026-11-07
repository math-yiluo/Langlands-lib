# Normalized inverse kernels on finite-dimensional manifold groups

Worker 116 states
`Langlands.Analysis.SmoothNormalizedInverseKernelStatement`.
The model space and group have two independent universes.

Let `G` be a Hausdorff topological group equipped with a real smooth manifold
structure modelled on a finite-dimensional real normed space `V`. The topology
used for the manifold, group, supports and neighborhoods is the same original
topology. Smoothness of the group operations is not needed in this statement.
Give `G` its Borel measurable structure and fix a measure `μ` finite on compact
sets and positive on nonempty open sets.

For every identity neighborhood `U`, including neighborhoods that are not open,
there exists a real smooth function `κ : G → ℝ` with compact topological
support contained in `U`. It is nonnegative everywhere and strictly positive
at the identity. Its inverse kernel `g ↦ κ(g⁻¹)` is integrable for the original
measure and has real integral one.

This is an internal analytic generalization of the local bump construction
already used by
`Langlands.Global.ArchimedeanGL.normalizedCompactKernel` in
`Langlands.Global.ArchimedeanNormalizedKernelProof`. The existing theorem
keeps its original completion-based general linear group, coordinate smooth
carrier and complex kernel subtype. This statement is on arbitrary actual
finite-dimensional manifold groups and uses real scalar functions. It does
not change that theorem or assert a formal carrier comparison with it.

The proposed proof chooses a manifold smooth bump whose closed support is in
`U`, using the pinned Mathlib
`SmoothBumpFunction.nhds_basis_tsupport`. The bump equals one at the identity.
Inversion is a homeomorphism, so its inverse kernel is continuous with compact
support. Compact finiteness makes that function integrable; positivity on
open sets and its nonzero identity value make its integral strictly positive.
Multiplying the original bump by the reciprocal of this integral gives all
the requested properties. The proposition records this proof obligation;
this file supplies no proof.

The inverse-integral convention is the one needed by the existing
left-Haar smoothing formula
`p ↦ ∫ y, κ(y⁻¹*p) • π(y)x ∂μ`: its integrated vector uses the weight
`g ↦ κ(g⁻¹)`. Normalization here uses no measure substitution. There is no
left or right invariance, inversion invariance, unimodularity, fixed Haar
normalization, global countability or positive-dimension assumption.
The open-positive hypothesis rules out the zero measure, including when the
model is zero-dimensional.

This statement constructs neither a concentrating sequence nor smooth-vector
density, an automorphic realization, compact-conjugation invariance, modular
symmetry, self-adjointness or compactness of an integrated operator.
