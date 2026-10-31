/-
Ported from `Theorems/Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.RingTheory.Noetherian.Basic
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Finite_of_ker_le_range_of_isNoetherianRing
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


theorem Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂] (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M := by exact @_root_.P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution R _ _ M N₁ N₂ _ _ _ _ _ _ _ _ α β h
