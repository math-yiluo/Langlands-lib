/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Module.Finite R (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Module.Finite R (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Module.Finite R (ProjSpaceCech.GradedModule.H D i) := by exact @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.solution R _ _ n D σ i hF hK
