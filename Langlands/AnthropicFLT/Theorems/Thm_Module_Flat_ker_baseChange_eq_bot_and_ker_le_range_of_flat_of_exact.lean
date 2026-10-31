/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Ported by Worker 137 from Anthropic FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Theorems/Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.lean.
Changes: FLT imports moved under Langlands.AnthropicFLT; P2M.Util removed;
P2M commands replaced by standard Lean commands; finite port options added.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact
    {R : Type u} [CommRing R] (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
    [∀ i, Module.Flat R (C i)] (d : ∀ i, C i →ₗ[R] C (i + 1))
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (h0 : LinearMap.ker (d 0) = ⊥) (hex : ∀ i, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i))
    (A : Type u) [CommRing A] [Algebra R A] :
    LinearMap.ker ((d 0).baseChange A) = ⊥ ∧
      ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by
  exact _root_.P2MW.S_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact.solution C d hdd n hbd h0 hex A
