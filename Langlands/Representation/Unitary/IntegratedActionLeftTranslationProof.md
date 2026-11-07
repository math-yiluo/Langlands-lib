# Left translation of the integrated isometric action

`Langlands.Analysis.integratedActionLeftTranslation` proves the unchanged
published `Langlands.Analysis.IntegratedActionLeftTranslationStatement`
in the two independent universes of its original group and Banach space.
Worker 116 developed the proof in the parent task's revision 53 draft;
Worker 1822 adopted that exact Lean file and prepared this focused contribution.

The translated scalar function is integrable by `Integrable.comp_mul_left`.
The public constructor's `isometricActionIntegrand_integrable` then proves
integrability of the translated weighted orbit. For the equality, the proof
unfolds the constructor's application formula and commutes `π(p)` with the
Bochner integral using `ContinuousLinearMap.integral_comp_comm`. Linearity
and `π.map_mul` identify this integrand with the left translate of
`y ↦ f(p⁻¹*y) • π(y)x`. `integral_mul_left_eq_self` removes that translation.
Every step uses the original measure, scalar function, action and vector.

This is an internal consequence of the existing constructor and left invariant
Bochner integration. It does not require inversion or right invariance of the
measure. For inverse kernels the group identity
`(p⁻¹*y)⁻¹ = y⁻¹*p` gives the convolution order required for the orbit map.
Smoothness and approximation are separate results.

The proof imports the published statement and operator by Lean module name.
It adds no hypotheses to the statement and preserves the multiplication
order `p⁻¹*y` in its translated scalar weight.
