/-
Ported from `Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module imports are prefixed by `Langlands.AnthropicFLT`; the import of `P2M.Util` is
dropped; the FLT lakefile options are set after the imports; the `p2m_exact_reverting` proof is
replaced by the solution term. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

open scoped Classical in

theorem BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) :=
  P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.solution ρ
