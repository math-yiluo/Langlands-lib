/-
Ported from `Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module imports are prefixed by `Langlands.AnthropicFLT`; the import of `P2M.Util` is
dropped; the FLT lakefile options are set after the imports; the `p2m_exact_reverting` proof is
replaced by the solution term. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced
import Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

open scoped Classical in

theorem ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
    {G : Type} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime) (A : Subgroup G) (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hquot : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A)
    {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g :=
  P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.solution hp A hA hcomm hquot ρ
