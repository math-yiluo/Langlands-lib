import Langlands.Global.RankinSelberg.RealSlotLevi
import Langlands.Representation.Archimedean.RealLeviShear
import Langlands.Global.RankinSelberg.RealGodementStepChart

/-! # The open cell in Levi coordinates of a slot set -/

noncomputable section

open MeasureTheory Matrix
open Langlands.Archimedean
open Langlands.Archimedean.RealLeviChartIntegrable Langlands.Archimedean.RealLeviTwoBlock
open Langlands.Archimedean.RealLeviBorel Langlands.Archimedean.RealLeviLeviBorel
open Langlands.Archimedean.RealLeviShear

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {N : ℕ}

namespace SlotSet

variable (S : SlotSet N)

/-! ## The block index -/

/-- The block index of a position: the number of earlier positions that do not start a slot.
The two positions of a slot have the same index; every other position is a block of its own. -/
def blockIdx (i : Fin N) : ℕ := ((Finset.range i).filter (· ∉ S.starts)).card

variable {S}

theorem blockIdx_le_of_le {i j : Fin N} (h : i ≤ j) : S.blockIdx i ≤ S.blockIdx j :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

theorem blockIdx_monotone : Monotone S.blockIdx := fun _ _ h => blockIdx_le_of_le h

theorem blockIdx_lt_of_lt {i j : Fin N} (hji : j < i) (h : ¬ ((j : ℕ) ∈ S.starts ∧ (i : ℕ) = j + 1)) :
    S.blockIdx j < S.blockIdx i := by
  have hji' : (j : ℕ) < i := hji
  obtain ⟨k, hk1, hk2, hk3⟩ : ∃ k : ℕ, (j : ℕ) ≤ k ∧ k < i ∧ k ∉ S.starts := by
    by_cases hj : (j : ℕ) ∈ S.starts
    · refine ⟨j + 1, by omega, ?_, S.sep _ hj⟩
      by_contra hc
      exact h ⟨hj, by omega⟩
    · exact ⟨j, le_rfl, hji', hj⟩
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hji'.le), fun hsub => ?_⟩
  have hk : k ∈ (Finset.range i).filter (· ∉ S.starts) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk2, hk3⟩
  have := Finset.mem_range.mp (Finset.mem_filter.mp (hsub hk)).1
  omega

theorem blockIdx_second {p : ℕ} (hp : p ∈ S.starts) :
    S.blockIdx (second hp) = S.blockIdx (first hp) := by
  simp only [blockIdx, second, first, Finset.range_add_one, Finset.filter_insert, hp,
    not_true_eq_false, ite_false]

theorem eq_of_blockIdx_eq {i j : Fin N} (hji : j < i) (h : S.blockIdx i = S.blockIdx j) :
    (j : ℕ) ∈ S.starts ∧ (i : ℕ) = j + 1 := by
  by_contra hc
  exact absurd h (Nat.ne_of_gt (blockIdx_lt_of_lt hji hc))

theorem blockIdx_perm (i : Fin N) : S.blockIdx (S.perm i) = S.blockIdx i := by
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · have hsw := S.inSlot_swapFun h
    have hσ : S.perm i = S.swapFun i := rfl
    have hp : p ∈ S.starts := h.1
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · have hi : i = first hp := Fin.ext (by simpa [first] using h.2)
      have hs : S.perm i = second hp := Fin.ext (by rw [hσ]; simpa [second] using hsw.2)
      rw [hs, hi, blockIdx_second]
    · have hi : i = second hp := Fin.ext (by simpa [second] using h.2)
      have hs : S.perm i = first hp := Fin.ext (by rw [hσ]; simpa [first] using hsw.2)
      rw [hs, hi, blockIdx_second]
  · have : S.perm i = i := S.not_inSlot_swapFun h
    rw [this]

/-! ## The coordinates inside the blocks -/

/-- The coordinates inside the blocks are the slots. -/
def coordMEquiv : CoordM S.blockIdx ≃ S.starts where
  toFun x := ⟨x.1.2, (eq_of_blockIdx_eq x.2.2 x.2.1).1⟩
  invFun q := ⟨(second q.2, first q.2), blockIdx_second q.2, by
    change (q : ℕ) < q + 1
    omega⟩
  left_inv x := by
    obtain ⟨⟨p, q⟩, h1, h2⟩ := x
    have h := eq_of_blockIdx_eq h2 h1
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (show (q : ℕ) + 1 = p from h.2.symm)
    · exact Fin.ext (by simp [first])
  right_inv q := rfl

theorem coordMEquiv_symm_val (q : S.starts) :
    ((coordMEquiv.symm q : CoordM S.blockIdx) : Fin N × Fin N) = (second q.2, first q.2) := rfl

/-- The block coordinates as slot coordinates. -/
def slotOfM (Z : CoordM S.blockIdx → ℝ) : S.starts → ℝ := fun q => Z (coordMEquiv.symm q)

theorem piCongrLeft_coordMEquiv :
    (MeasurableEquiv.piCongrLeft (fun _ : S.starts => ℝ) (coordMEquiv (S := S)) :
      (CoordM S.blockIdx → ℝ) → (S.starts → ℝ)) = slotOfM := by
  funext Z q
  obtain ⟨x, rfl⟩ := (coordMEquiv (S := S)).surjective q
  change Equiv.piCongrLeft (fun _ => ℝ) coordMEquiv Z (coordMEquiv x) = _
  rw [Equiv.piCongrLeft_apply_apply]
  simp [slotOfM]

theorem measurePreserving_slotOfM :
    MeasurePreserving (slotOfM (S := S)) volume volume := by
  rw [← piCongrLeft_coordMEquiv]
  exact measurePreserving_piCongrLeft (fun _ : S.starts => (volume : Measure ℝ))
    (coordMEquiv (S := S))

theorem integral_comp_slotOfM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (S.starts → ℝ) → E) : ∫ Z, F (slotOfM Z) = ∫ x, F x := by
  have h := (measurePreserving_piCongrLeft (fun _ : S.starts => (volume : Measure ℝ))
    (coordMEquiv (S := S))).integral_comp' F
  rw [← piCongrLeft_coordMEquiv]
  exact h

/-- A matrix description of the slot unipotent conjugated by the slot swap. -/
theorem swap2_mul_upper2_mul_swap2 (x : ℝ) :
    ((swap2 * upper2 x * swap2 : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap2, upper2, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The block lower unitriangular matrix of the slot set** is the slot unipotent conjugated
by the slot swap. -/
theorem lowerMGL_eq (Z : CoordM S.blockIdx → ℝ) :
    lowerMGL S.blockIdx Z = S.swapGL * S.unip (S.ext (slotOfM Z)) * S.swapGL := by
  have hd : S.swapGL * S.unip (S.ext (slotOfM Z)) * S.swapGL =
      S.diagGL fun p => swap2 * upper2 (S.ext (slotOfM Z) p) * swap2 := by
    simp only [swapGL, unip, diagGL_mul]
  rw [hd]
  apply Units.ext
  ext i j
  rw [lowerMGL_val]
  change lowerM S.blockIdx Z i j =
    S.diag (fun p => ((swap2 * upper2 (S.ext (slotOfM Z) p) * swap2 :
      Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) i j
  simp only [swap2_mul_upper2_mul_swap2]
  rcases S.inSlot_or i with ⟨p, o, h⟩ | h
  · rw [diag_row _ h]
    have hp := h.1
    have hsep := S.sep p hp
    obtain rfl | rfl : o = 0 ∨ o = 1 := by fin_cases o <;> simp
    · have hi : (i : ℕ) = p := by simpa using h.2
      have hn : ¬ (S.blockIdx i = S.blockIdx j ∧ j < i) := by
        rintro ⟨he, hlt⟩
        have := eq_of_blockIdx_eq hlt he
        rw [hi] at this
        exact S.not_mem_pred (this.2 ▸ hp) this.1
      simp only [lowerM, of_apply, dite_eq_right_iff.mpr (fun h' => absurd h' hn)]
      by_cases hj : (j : ℕ) = p
      · have : i = j := Fin.ext (by omega)
        simp [this, hj]
      · by_cases hj' : (j : ℕ) = p + 1
        · have : i ≠ j := fun e => by rw [e] at hi; omega
          simp [this, hj']
        · have : i ≠ j := fun e => by rw [e] at hi; omega
          simp [this, hj, hj']
    · have hi : (i : ℕ) = p + 1 := by simpa using h.2
      by_cases hj : (j : ℕ) = p
      · have hjf : j = first hp := Fin.ext (by simp [first, hj])
        have hif : i = second hp := Fin.ext (by simp [second, hi])
        have hc : S.blockIdx i = S.blockIdx j ∧ j < i := by
          rw [hjf, hif]
          exact ⟨blockIdx_second hp, by change p < p + 1; omega⟩
        simp only [lowerM, of_apply, hj, ite_true]
        rw [dite_eq_left hc]
        simp only [Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val',
          Matrix.cons_val_fin_one]
        simp only [SlotSet.ext, hp, dite_true, slotOfM]
        congr 1
        apply Subtype.ext
        rw [coordMEquiv_symm_val, ← hif, ← hjf]
      · have hn : ¬ (S.blockIdx i = S.blockIdx j ∧ j < i) := by
          rintro ⟨he, hlt⟩
          have := eq_of_blockIdx_eq hlt he
          omega
        simp only [lowerM, of_apply, dite_eq_right_iff.mpr (fun h' => absurd h' hn), hj, ite_false]
        by_cases hj' : (j : ℕ) = p + 1
        · have : i = j := Fin.ext (by omega)
          simp [this, hj']
        · have : i ≠ j := fun e => by rw [e] at hi; omega
          simp [this, hj']
  · rw [diag_row_other _ h]
    have hn : ¬ (S.blockIdx i = S.blockIdx j ∧ j < i) := by
      rintro ⟨he, hlt⟩
      have := eq_of_blockIdx_eq hlt he
      exact h j 1 ⟨this.1, by simp [this.2]⟩
    simp only [lowerM, of_apply, dite_eq_right_iff.mpr (fun h' => absurd h' hn), eq_comm]

end SlotSet

/-! ## Conjugating the opposite radical by a block permutation -/

section Conj

variable {ι : Type*} [LinearOrder ι] {cl : Fin N → ι}

/-- The coordinates permuted by a permutation of the positions preserving the blocks. -/
def permCoord (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, cl (σ i) = cl i) : CoordC cl ≃ CoordC cl where
  toFun x := ⟨(σ.symm x.1.1, σ.symm x.1.2), by
    have h1 := hσ (σ.symm x.1.1)
    have h2 := hσ (σ.symm x.1.2)
    simp only [Equiv.apply_symm_apply] at h1 h2
    change cl (σ.symm x.1.2) < cl (σ.symm x.1.1)
    rw [← h1, ← h2]
    exact x.2⟩
  invFun x := ⟨(σ x.1.1, σ x.1.2), by
    change cl (σ x.1.2) < cl (σ x.1.1)
    rw [hσ, hσ]
    exact x.2⟩
  left_inv x := by simp
  right_inv x := by simp

theorem permutation_mul_lowerCGL (hcl : Monotone cl) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i, cl (σ i) = cl i) (X : CoordC cl → ℝ) :
    (Langlands.GeneralLinear.permutation N ℝ σ : Langlands.GeneralLinear N ℝ) * lowerCGL hcl X =
      lowerCGL hcl (X ∘ permCoord σ hσ) *
        (Langlands.GeneralLinear.permutation N ℝ σ : Langlands.GeneralLinear N ℝ) := by
  rw [← mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  have h := Langlands.GeneralLinear.permutation_conjugate_entry N ℝ σ (lowerCGL hcl X) i j
  refine h.trans ?_
  change lowerC cl X (σ⁻¹ i) (σ⁻¹ j) = lowerC cl (X ∘ permCoord σ hσ) i j
  have hi := hσ (σ⁻¹ i)
  have hj := hσ (σ⁻¹ j)
  rw [show σ (σ⁻¹ i) = i by simp] at hi
  rw [show σ (σ⁻¹ j) = j by simp] at hj
  simp only [lowerC, of_apply]
  by_cases hc : cl j < cl i
  · have hc' : cl (σ⁻¹ j) < cl (σ⁻¹ i) := by rw [hi, hj] at hc; exact hc
    rw [dite_eq_left hc', dite_eq_left hc]
    rfl
  · have hc' : ¬ cl (σ⁻¹ j) < cl (σ⁻¹ i) := by rw [hi, hj] at hc; exact hc
    rw [dite_eq_right hc', dite_eq_right hc]
    simp only [EmbeddingLike.apply_eq_iff_eq]

theorem piCongrLeft_permCoord (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, cl (σ i) = cl i) :
    (MeasurableEquiv.piCongrLeft (fun _ : CoordC cl => ℝ) (permCoord σ hσ).symm :
      (CoordC cl → ℝ) → (CoordC cl → ℝ)) = fun X => X ∘ permCoord σ hσ := by
  funext X x
  obtain ⟨y, rfl⟩ := (permCoord σ hσ).symm.surjective x
  change Equiv.piCongrLeft (fun _ => ℝ) (permCoord σ hσ).symm X ((permCoord σ hσ).symm y) = _
  rw [Equiv.piCongrLeft_apply_apply]
  simp

theorem measurePreserving_comp_permCoord (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, cl (σ i) = cl i) :
    MeasurePreserving (fun X : CoordC cl → ℝ => X ∘ permCoord σ hσ) volume volume := by
  rw [← piCongrLeft_permCoord]
  exact measurePreserving_piCongrLeft (fun _ : CoordC cl => (volume : Measure ℝ))
    (permCoord σ hσ).symm

theorem integral_comp_permCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, cl (σ i) = cl i) (F : (CoordC cl → ℝ) → E) :
    ∫ X, F (X ∘ permCoord σ hσ) = ∫ X, F X := by
  have h := (measurePreserving_piCongrLeft (fun _ : CoordC cl => (volume : Measure ℝ))
    (permCoord σ hσ).symm).integral_comp' F
  simp only [piCongrLeft_permCoord] at h
  exact h

end Conj

end Langlands.Global.RankinSelbergGlobal.RealLeviStages
