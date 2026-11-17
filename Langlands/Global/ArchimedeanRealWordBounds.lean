import Langlands.Global.ArchimedeanOrbitDerivativeInterchange
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Normed.Module.Basic

/-! # Finite real-word bounds for the actual archimedean enveloping algebra -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] (n : ℕ)

/-- A word of real Lie directions in the actual complex enveloping algebra. -/
def realEnvelopingWord (xs : List (RealLieAlgebra F n)) : EnvelopingAlgebra F n :=
  (xs.map fun X => envelopingGenerator F n (complexify F n X)).prod

@[simp]
theorem realEnvelopingWord_nil : realEnvelopingWord F n [] = 1 := rfl

@[simp]
theorem realEnvelopingWord_cons (X : RealLieAlgebra F n) (xs : List (RealLieAlgebra F n)) :
    realEnvelopingWord F n (X :: xs) =
      envelopingGenerator F n (complexify F n X) * realEnvelopingWord F n xs := rfl

/-- Real Lie words span the actual complex enveloping algebra. -/
theorem mem_span_realEnvelopingWord (a : EnvelopingAlgebra F n) :
    a ∈ Submodule.span ℂ (Set.range (realEnvelopingWord F n)) := by
  apply enveloping_real_left_induction F n
  · exact Submodule.subset_span ⟨[], rfl⟩
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb
  · intro z a ha
    exact Submodule.smul_mem _ z ha
  · intro X a ha
    refine Submodule.span_induction
      (p := fun a _ => envelopingGenerator F n (complexify F n X) * a ∈
        Submodule.span ℂ (Set.range (realEnvelopingWord F n))) ?_ ?_ ?_ ?_ ha
    · rintro a ⟨xs, rfl⟩
      exact Submodule.subset_span ⟨X :: xs, rfl⟩
    · simpa only [mul_zero] using
        (Submodule.span ℂ (Set.range (realEnvelopingWord F n))).zero_mem
    · intro a b _ _ ha hb
      simpa only [mul_add] using Submodule.add_mem _ ha hb
    · intro z a _ ha
      simpa only [mul_smul_comm] using Submodule.smul_mem _ z ha

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (A : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V) (j : V →ₗ[ℂ] E)

/-- For any algebra action and linear map into a normed space, one actual
enveloping operator is bounded by finitely many real-word operators. -/
theorem norm_enveloping_le_realWords (a : EnvelopingAlgebra F n) :
    ∃ (S : Finset (List (RealLieAlgebra F n))) (C : ℝ), 0 ≤ C ∧
      ∀ v : V, ‖j (A a v)‖ ≤ C * ∑ xs ∈ S, ‖j (A (realEnvelopingWord F n xs) v)‖ := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (mem_span_realEnvelopingWord F n a)
  let C : ℝ := ∑ xs ∈ c.support, ‖c xs‖
  refine ⟨c.support, C, Finset.sum_nonneg (fun xs _ => norm_nonneg _), ?_⟩
  intro v
  have he : j (A a v) =
      ∑ xs ∈ c.support, c xs • j (A (realEnvelopingWord F n xs) v) := by
    rw [← hc]
    simp only [Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [he]
  calc
    ‖∑ xs ∈ c.support, c xs • j (A (realEnvelopingWord F n xs) v)‖ ≤
        ∑ xs ∈ c.support, ‖c xs • j (A (realEnvelopingWord F n xs) v)‖ := norm_sum_le _ _
    _ ≤ ∑ xs ∈ c.support, C * ‖j (A (realEnvelopingWord F n xs) v)‖ := by
      apply Finset.sum_le_sum
      intro xs hxs
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun ys _ => norm_nonneg (c ys)) hxs) (norm_nonneg _)
    _ = C * ∑ xs ∈ c.support, ‖j (A (realEnvelopingWord F n xs) v)‖ :=
      (Finset.mul_sum _ _ _).symm

/-- One finite family of actual enveloping operators is controlled by a
single finite family of real-word operators, uniformly over the vector. -/
theorem sum_norm_enveloping_le_realWords (D : Finset (EnvelopingAlgebra F n)) :
    ∃ (S : Finset (List (RealLieAlgebra F n))) (C : ℝ), 0 ≤ C ∧
      ∀ v : V, ∑ d ∈ D, ‖j (A d v)‖ ≤
        C * ∑ xs ∈ S, ‖j (A (realEnvelopingWord F n xs) v)‖ := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, 0, le_rfl, by simp⟩
  | @insert a D ha ih =>
    obtain ⟨S, C, hC, hbound⟩ := norm_enveloping_le_realWords F n A j a
    obtain ⟨T, B, hB, hrest⟩ := ih
    refine ⟨S ∪ T, C + B, add_nonneg hC hB, ?_⟩
    intro v
    have hs : (∑ xs ∈ S, ‖j (A (realEnvelopingWord F n xs) v)‖) ≤
        ∑ xs ∈ S ∪ T, ‖j (A (realEnvelopingWord F n xs) v)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun _ _ _ => norm_nonneg _)
    have ht : (∑ xs ∈ T, ‖j (A (realEnvelopingWord F n xs) v)‖) ≤
        ∑ xs ∈ S ∪ T, ‖j (A (realEnvelopingWord F n xs) v)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun _ _ _ => norm_nonneg _)
    rw [Finset.sum_insert ha]
    exact (add_le_add (hbound v) (hrest v)).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hs hC)
        (mul_le_mul_of_nonneg_left ht hB)).trans_eq (add_mul _ _ _).symm)

end Langlands.Global.ArchimedeanGL
