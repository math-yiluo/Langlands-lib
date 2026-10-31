/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.nonempty_HEquiv_pi {R : Type u} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] (D : ι → ProjSpaceCech.GradedModule R n) (i : ℕ) :
    Nonempty (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi D) i ≃ₗ[R] (∀ k, ProjSpaceCech.GradedModule.H (D k) i)) := by exact @_root_.P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.solution R _ n ι _ D i
