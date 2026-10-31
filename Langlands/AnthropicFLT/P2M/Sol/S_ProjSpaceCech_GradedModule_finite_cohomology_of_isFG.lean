/-
Ported from `P2M/Sol/S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
export _root_.ProjSpaceCech (GradedModule GradedModule.H GradedModule.subsingleton_cohomology_of_lt GradedModule.Presentation GradedModule.IsFG GradedModule.Presentation.finite_H_of_ses GradedModule.Presentation.ker_isFG GradedModule.finite_cohomology_pi_FD)
open _root_.ProjSpaceCech

section Main

variable {R : Type u} [CommRing R] {n : ℕ}

namespace GradedModule export _root_.ProjSpaceCech.GradedModule (H subsingleton_cohomology_of_lt Presentation IsFG Presentation.finite_H_of_ses Presentation.ker_isFG finite_cohomology_pi_FD) end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in

theorem GradedModule.finite_cohomology_of_isFG' [IsNoetherianRing R] (D : GradedModule R n)
    (hD : GradedModule.IsFG D) (i : ℕ) :
    Module.Finite R (GradedModule.H D i) := by

  suffices h : ∀ i, ∀ (D' : GradedModule R n), GradedModule.IsFG D' →
      Module.Finite R (GradedModule.H D' i) from h i D hD
  intro i
  induction i using Nat.strong_decreasing_induction with
  | base =>
    refine ⟨n, fun m hm D' _ => ?_⟩
    haveI := GradedModule.subsingleton_cohomology_of_lt D' hm
    infer_instance
  | step i IH =>
    intro D' ⟨σ⟩
    refine GradedModule.Presentation.finite_H_of_ses σ i ?_ ?_
    · exact GradedModule.finite_cohomology_pi_FD R n σ.d₀ i
    · exact IH (i + 1) (Nat.lt_succ_self i) σ.ker (GradedModule.Presentation.ker_isFG σ)

end Main

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n)
    (hD : ProjSpaceCech.GradedModule.IsFG D) (i : ℕ) : Module.Finite R (ProjSpaceCech.GradedModule.H D i) :=
  ProjSpaceCech.GradedModule.finite_cohomology_of_isFG' D hD i

end
