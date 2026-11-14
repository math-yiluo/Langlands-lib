# Nonzero sections of large twists on nonempty fibres

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistSections` (namespace
`Langlands.AlgebraicGeometry.Modules.FibreTwist`) proves clause 2 of
`ProjectiveFibreTwistCohomologyStatement`.

## Lemmas

- `nontrivial_sections_of_isInvertible`: an invertible module has nonzero sections over every
  nonempty affine open `W`. By the FLT theorem `IsInvertible.dual_monoidalV2`,
  `M ⊗ M^∨ ≅ 𝒪`. On the affine `W`, `Γ(M, W) ⊗ Γ(M^∨, W) ≅ Γ(M ⊗ M^∨, W)` (FLT
  `bijective_lift_tensorSectionsBilin_monoidalV2`). If `Γ(M, W)` were zero, then `Γ(X, W)` would
  be zero, contradicting Mathlib's `Scheme.component_nontrivial`.
- `not_isZero_homology_zero`: a nonzero Čech `0`-cocycle gives nonzero Čech homology in degree `0`
  (no incoming differential at degree `0`). `not_isZero_homology_zero_of_iso` transports this along
  isomorphisms of complexes.
- `not_isZero_cech_twist`: global generation data in the form of the FLT theorem
  `OModulePresheaf.exists_forall_exists_H0_tensor_twist_span_eq_top` give nonzero degree-zero Čech
  homology of `ofModules F ⊗ O(d)` on a nonempty scheme. A point lies in a chart `W` of the
  pulled-back standard cover. There `ofModules F ⊗ O(d)` has nonzero sections: it is isomorphic to
  `Γ(F ⊗ L^{⊗ d}, W)` through the maps of `TwistCechBridge`, and this is nonzero by the first
  lemma. So one of the generating global sections is nonzero.
- `not_isZero_cech_tensor_of_twist`, `not_isZero_relativeCohomology_zero_of_cech`: transfer the
  nonvanishing to `ofModules F ⊗ ofModules(L^{⊗ d})`, to `ofModules(F ⊗ L^{⊗ d})`, and to the
  actual `H⁰` (Library `CechResolution.cechCohomologyIso`).
- `exists_not_isZero_relativeCohomology_zero`: on a nonempty scheme separated over `Spec A`, with
  a presentation whose morphism to `ℙᴺ_A` is a closed immersion, `H⁰(F ⊗ L^{⊗ d}) ≠ 0` for all large
  `d`.

## Clause 2

`nonzeroSections_of_point` treats the base change of `X_T ⟶ T` along an arbitrary point
`b : Spec B ⟶ T`. The presentation of `𝓛X` is base changed along `Spec B ⟶ Spec A` (FLT
`exists_baseChange_of_isPullback`, as in clause 1). Then `exists_not_isZero_relativeCohomology_zero`
applies, with `pullbackTwistIso` and `twistTensorPowIso` identifying the restriction of `F(n)`.
`nonzeroSections` is the case `b = T.fromSpecResidueField t`, the fibre over `t`. Working with a
general `B` avoids conflicting ring structures on the residue field.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
