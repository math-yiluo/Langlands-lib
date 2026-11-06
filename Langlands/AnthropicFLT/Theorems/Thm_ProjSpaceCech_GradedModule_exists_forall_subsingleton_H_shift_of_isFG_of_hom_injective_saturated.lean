/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D)
    (h : ProjSpaceCech.GradedModule.Hom D M) (hinj : Function.Injective h.toLinearMap)
    (hsat : ∀ (e : ℤ) (f : M.M), f ∈ M.grade e → ∀ j : Fin (n + 1),
      ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧ h.toLinearMap f' = (M.xMul j ^ N) f) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) :=
  P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.solution M D hD h hinj hsat
