import Langlands.Global.GlobalCompletionWeakApproximation

/-! # Weak approximation in real completions -/

noncomputable section

universe u

open NumberField

namespace Langlands.Global

section NumberField

variable (F : Type u) [Field F] [NumberField F]

/-- The diagonal into the product of the real completions is dense. -/
theorem denseRange_realCompletionDiagonal :
    DenseRange (fun a : F => fun w : {w : InfinitePlace F // w.IsReal} =>
      algebraMap F w.1.Completion a) := by
  classical
  let project (a : (∀ w : InfinitePlace F, w.Completion) ×
      (∀ v : (∅ : Finset (FinitePlace F)), FiniteCompletion F v.1)) :
      ∀ w : {w : InfinitePlace F // w.IsReal}, w.1.Completion := fun w => a.1 w.1
  have hproj : Function.Surjective project := by
    intro a
    refine ⟨⟨fun w => if h : w.IsReal then a ⟨w, h⟩ else 0, fun _ => 0⟩, ?_⟩
    funext w
    exact dite_eq_left w.2
  have hcont : Continuous project :=
    continuous_pi fun w => (continuous_apply w.1).comp continuous_fst
  exact hproj.denseRange.comp (denseRange_numberFieldFiniteCompletionDiagonal F ∅) hcont

/-- Weak approximation for any finite number of affine coordinates at the real places. -/
def RealCompletionVectorWeakApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ),
    DenseRange (fun a : Fin n → F => fun w : {w : InfinitePlace F // w.IsReal} =>
      fun i => algebraMap F w.1.Completion (a i))

theorem realCompletionVectorWeakApproximation : RealCompletionVectorWeakApproximationStatement.{u} := by
  intro K _ _ n
  let transpose (a : Fin n → ∀ w : {w : InfinitePlace K // w.IsReal}, w.1.Completion) :
      ∀ w : {w : InfinitePlace K // w.IsReal}, Fin n → w.1.Completion := fun w i => a i w
  have hsurj : Function.Surjective transpose := fun a => ⟨fun i w => a w i, rfl⟩
  have hcont : Continuous transpose :=
    continuous_pi fun w => continuous_pi fun i => (continuous_apply w).comp (continuous_apply i)
  exact hsurj.denseRange.comp (DenseRange.piMap fun _ : Fin n =>
    denseRange_realCompletionDiagonal K) hcont

/-- A nonzero element of the number field can realize any prescribed signs at the real places. -/
theorem exists_realPlace_signs
    (negative : Set {w : InfinitePlace F // w.IsReal}) :
    ∃ a : F, a ≠ 0 ∧
      (∀ w : {w : InfinitePlace F // w.IsReal},
        w ∈ negative → InfinitePlace.embedding_of_isReal w.2 a < 0) ∧
      (∀ w : {w : InfinitePlace F // w.IsReal},
        w ∉ negative → 0 < InfinitePlace.embedding_of_isReal w.2 a) := by
  classical
  by_cases h : Nonempty {w : InfinitePlace F // w.IsReal}
  · let U (w : {w : InfinitePlace F // w.IsReal}) : Set w.1.Completion :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2) ⁻¹'
        (if w ∈ negative then Set.Iio 0 else Set.Ioi 0)
    have hU (w) : IsOpen (U w) := by
      apply IsOpen.preimage
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous
      split_ifs
      · exact isOpen_Iio
      · exact isOpen_Ioi
    have hUn (w) : (U w).Nonempty := by
      apply Set.Nonempty.preimage
      · split_ifs
        · exact ⟨-1, by norm_num⟩
        · exact ⟨1, by norm_num⟩
      · exact InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal w.2
    obtain ⟨a, ha⟩ := (denseRange_realCompletionDiagonal F).exists_mem_open
      (isOpen_set_pi Set.finite_univ (fun w _ => hU w)) (Set.univ_pi_nonempty_iff.mpr hUn)
    have hsign (w : {w : InfinitePlace F // w.IsReal}) :
        if w ∈ negative then InfinitePlace.embedding_of_isReal w.2 a < 0
        else 0 < InfinitePlace.embedding_of_isReal w.2 a := by
      have hw := ha w (Set.mem_univ _)
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((WithAbs.equiv w.1.1).symm a : w.1.Completion) ∈
          (if w ∈ negative then Set.Iio 0 else Set.Ioi 0) at hw
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply] at hw
      split_ifs at hw ⊢ <;> exact hw
    refine ⟨a, ?_, fun w hw => ?_, fun w hw => ?_⟩
    · intro ha0
      obtain ⟨w⟩ := h
      by_cases hw : w ∈ negative <;> simpa [ha0, hw] using hsign w
    · simpa only [ite_eq_left hw] using hsign w
    · simpa only [ite_eq_right hw] using hsign w
  · exact ⟨1, one_ne_zero, fun w => (h ⟨w⟩).elim, fun w => (h ⟨w⟩).elim⟩

end NumberField

end Langlands.Global
