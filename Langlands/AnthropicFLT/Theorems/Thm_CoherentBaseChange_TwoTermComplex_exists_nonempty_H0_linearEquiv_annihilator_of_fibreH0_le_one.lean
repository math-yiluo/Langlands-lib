/-
Ported from `Theorems/Thm_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
    (𝔭 : PrimeSpectrum R) (h𝔭 : G.fibreH0 𝔭 ≤ 1) :
    ∃ (h : R) (J : Ideal R), h ∉ 𝔭.asIdeal ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B], IsUnit (algebraMap R B h) →
        Nonempty (G.H0 B ≃ₗ[B] (J.map (algebraMap R B)).annihilator) := by exact @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution R _ G 𝔭 h𝔭
