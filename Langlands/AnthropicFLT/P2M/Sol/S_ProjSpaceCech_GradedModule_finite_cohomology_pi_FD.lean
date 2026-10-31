/-
Ported from `P2M/Sol/S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

theorem solution (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (d₀ : ι → ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi (fun k => ProjSpaceCech.GradedModule.FD R n (d₀ k))) i) :=
  by
  haveI : ∀ k, Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n (d₀ k)) i) :=
    fun k => ProjSpaceCech.GradedModule.finite_cohomology_FD R n (d₀ k) i
  obtain ⟨e⟩ := ProjSpaceCech.GradedModule.nonempty_HEquiv_pi (fun k => ProjSpaceCech.GradedModule.FD R n (d₀ k)) i
  exact Module.Finite.equiv e.symm

end
