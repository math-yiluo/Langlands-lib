/-
Ported from `Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module imports are prefixed by `Langlands.AnthropicFLT`; the import of `P2M.Util` is
dropped; the FLT lakefile options are set after the imports; the `p2m_exact_reverting` proof is
replaced by the solution term. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced
import Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
    {G : Type} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g :=
  P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.solution
