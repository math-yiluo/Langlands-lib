/-
Copyright 2026 Anthropic
Licensed under the Apache License, Version 2.0.
Ported by Worker 137 from Anthropic FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Theorems/Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.lean.
Changes: FLT imports moved under Langlands.AnthropicFLT; P2M.Util removed;
P2M commands replaced by standard Lean commands; finite port options added.
See licenses/Anthropic-FLT/LICENSE and licenses/Anthropic-FLT/NOTICE.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat
    {R : Type u} [CommRing R] {N M P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P]
    (A : Type u) [AddCommGroup A] [Module R A] :
    Function.Injective (f.lTensor A) := by
  exact _root_.P2MW.S_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat.solution f g hf hfg hg A
