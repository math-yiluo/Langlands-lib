/-
Ported from `Theorems/Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (g₀ : G.C0)
    (hker : ∀ x : G.C0, G.d x = 0 → ∃ r : R, x = r • g₀)
    (hH0 : ∀ (C : Type u) [CommRing C] [Algebra R C], Nonempty (G.H0 C ≃ₗ[C] C))
    (C : Type u) [CommRing C] [Algebra R C] [Nontrivial C] :
    ((1 : C) ⊗ₜ[R] g₀ : C ⊗[R] G.C0) ≠ 0 := by exact @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution R _ G g₀ hker hH0 C _ _ _
