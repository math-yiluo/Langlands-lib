/-
Ported from `Theorems/Thm_Coalgebra_exists_finiteDimensional_le_comul_mem_span.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Coalgebra.exists_finiteDimensional_le_comul_mem_span
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by
  exact _root_.P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.solution K hK x hx
