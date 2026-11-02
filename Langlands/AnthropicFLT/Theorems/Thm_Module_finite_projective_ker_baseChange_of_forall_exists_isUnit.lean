/-
Ported from `Theorems/Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Langlands.AnthropicFLT.P2M.Sol.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {C0 C1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup F] [Module R F]
    (δ : C0 →ₗ[R] C1) (Θ : F →ₗ[R] C0) (r : ℕ)
    (hloc : ∀ 𝔮 : PrimeSpectrum A, ∃ g : R, algebraMap R A g ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra R A'], IsUnit (algebraMap R A' g) →
        Module.Finite A' (LinearMap.ker (δ.baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (δ.baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk (LinearMap.ker (δ.baseChange A')) 𝔮' = r) ∧
        LinearMap.ker (δ.baseChange A') ≤ LinearMap.range (Θ.baseChange A')) :
    Module.Finite A (LinearMap.ker (δ.baseChange A)) ∧
    Module.Projective A (LinearMap.ker (δ.baseChange A)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (LinearMap.ker (δ.baseChange A)) 𝔮 = r) ∧
    LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A) :=
  P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.solution A δ Θ r hloc
