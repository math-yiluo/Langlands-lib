import Langlands.LinearAlgebra.ValuativeTraceBoundStatement

/-! # Trace probes bound every matrix entry -/

noncomputable section

universe u

open ValuativeRel

namespace Langlands

variable {F : Type u} [Field F] [ValuativeRel F]

private theorem exists_common_valuative_bound
    {I : Type*} [Fintype I] (b : I → F) (hb : ∀ i, b i ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ∀ i, b i ≤ᵥ c := by
  classical
  have h : ∀ s : Finset I, ∃ c : F, c ≠ 0 ∧ ∀ i ∈ s, b i ≤ᵥ c := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      rcases vle_total (b i) c with hi | hi
      · refine ⟨c, hc, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hi
        · exact hs j hj
      · refine ⟨b i, hb i, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact vle_rfl
        · exact (hs j hj).trans hi
  obtain ⟨c, hc, hs⟩ := h Finset.univ
  exact ⟨c, hc, fun i => hs i (Finset.mem_univ i)⟩

/-- Boundedness of traces extends from a family of probes to its linear span. -/
theorem exists_valuative_bound_trace_of_mem_span
    {N : ℕ} (S T : Set (Matrix (Fin N) (Fin N) F))
    (hT : ∀ B ∈ T, ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, (A * B).trace ≤ᵥ b)
    {B : Matrix (Fin N) (Fin N) F} (hB : B ∈ Submodule.span F T) :
    ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, (A * B).trace ≤ᵥ b := by
  induction hB using Submodule.span_induction with
  | mem B hB => exact hT B hB
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add B C _ _ hB hC =>
    obtain ⟨b, hb, hB⟩ := hB
    obtain ⟨c, hc, hC⟩ := hC
    rcases vle_total b c with hbc | hcb
    · refine ⟨c, hc, ?_⟩
      intro A hA
      rw [Matrix.mul_add, Matrix.trace_add]
      exact vle_add ((hB A hA).trans hbc) (hC A hA)
    · refine ⟨b, hb, ?_⟩
      intro A hA
      rw [Matrix.mul_add, Matrix.trace_add]
      exact vle_add (hB A hA) ((hC A hA).trans hcb)
  | smul a B _ hB =>
    by_cases ha : a = 0
    · subst a
      exact ⟨1, one_ne_zero, by simp⟩
    obtain ⟨b, hb, hB⟩ := hB
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    intro A hA
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] using
      mul_vle_mul_right (hB A hA) a

/-- Exact trace-probe bound, uniform over all entries and tested matrices. -/
theorem valuativeTraceBound_proof : ValuativeTraceBoundStatement.{u} := by
  intro F _ _ N S T hspan hT
  classical
  have hentry : ∀ i j : Fin N, ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, A i j ≤ᵥ b := by
    intro i j
    have hsingle : Matrix.single j i (1 : F) ∈ Submodule.span F T := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨b, hb, h⟩ := exists_valuative_bound_trace_of_mem_span S T hT hsingle
    exact ⟨b, hb, fun A hA => by simpa [Matrix.trace_mul_single] using h A hA⟩
  choose b hb hbound using hentry
  obtain ⟨c, hc, h⟩ := exists_common_valuative_bound
    (fun ij : Fin N × Fin N => b ij.1 ij.2) (fun ij => hb ij.1 ij.2)
  exact ⟨c, hc, fun A hA i j => (hbound i j A hA).trans (h (i, j))⟩

/-- In particular, integral traces against every spanning probe suffice. -/
theorem exists_valuative_bound_entries_of_trace_vle_one
    {N : ℕ} (S T : Set (Matrix (Fin N) (Fin N) F))
    (hspan : Submodule.span F T = ⊤)
    (hT : ∀ B ∈ T, ∀ A ∈ S, (A * B).trace ≤ᵥ (1 : F)) :
    ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, ∀ i j : Fin N, A i j ≤ᵥ b :=
  valuativeTraceBound_proof F N S T hspan
    (fun B hB => ⟨1, one_ne_zero, hT B hB⟩)

end Langlands
