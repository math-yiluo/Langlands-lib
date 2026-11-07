# Smooth vectors from the actual integrated isometric action: proof

Authors: Worker 116 and Worker 1650. Worker 116 developed the Lean proof in
the parent task's revision 55 draft; Worker 1650 adopted that exact Lean file
and prepared this focused contribution. The theorem
`Langlands.Analysis.integratedIsometricSmoothVectors` proves the unchanged
published `Langlands.Analysis.IntegratedIsometricSmoothVectorsStatement` at
its three independent carrier universes.

The proof first composes the smooth kernel's continuous function with
inversion. The inversion homeomorphism preserves compact support under
composition. `Continuous.integrable_of_hasCompactSupport` then proves
integrability of the inverse kernel for the original compact-finite measure.
This step uses no invariance under inversion.

For each original vector `x`, its continuous orbit is bundled as a continuous
map `w : C(G,E)`. `smoothCompactKernelConvolution` makes the literal function
`p ↦ ∫ y, κ(y⁻¹*p) • w(y) ∂μ` manifold smooth. The proved left translation
identity `integratedActionLeftTranslation`, specialized to the integrable
inverse kernel, identifies this function with the original orbit of the
actual `integratedIsometricAction` vector. The simplification uses
`(p⁻¹*y)⁻¹ = y⁻¹*p`. By the existing smooth-vector submodule definition, this
is exactly the required membership assertion.

All original action, measure, kernel, operator and vector data are retained.
The only measure change of variables lies in the left translation proof and
uses left invariance. Orbit measurability remains the original constructor's
explicit premise. The proof establishes no normalized kernel existence,
concentration, density or tensor realization.

This is an internal derived proof using the published integrated-action
left translation and smooth compact-kernel convolution theorems, imported
by Lean module name. It is not a transcription of an external source.
The theorem adds no hypotheses to the published statement and preserves
the original convolution order `y⁻¹*p`.
