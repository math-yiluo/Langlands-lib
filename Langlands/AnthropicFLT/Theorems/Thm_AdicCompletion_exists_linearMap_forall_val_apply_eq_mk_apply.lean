/-
Ported from `Theorems/Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] (I : Ideal A)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    ∃ θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N),
      ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
        Submodule.Quotient.mk g = x.val n →
          ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m) :=
  P2MW.S_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply.solution I M N
