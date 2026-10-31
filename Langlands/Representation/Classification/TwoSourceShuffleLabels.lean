import Langlands.Representation.Classification.UniformTargetBlockLabels
import Mathlib.Data.Fintype.Powerset

/-! Two source-block labels as shuffle subsets. -/

noncomputable section

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric

section Binary

variable {m : ℕ}

/-- The target blocks assigned to source label zero. -/
def binarySubset (lab : Fin m → Fin 2) : Finset (Fin m) :=
  Finset.univ.filter (fun i => lab i = 0)

/-- The binary label determined by a subset. -/
def binaryLabel (S : Finset (Fin m)) (i : Fin m) : Fin 2 :=
  if i ∈ S then 0 else 1

@[simp] theorem binarySubset_binaryLabel (S : Finset (Fin m)) :
    binarySubset (binaryLabel S) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [binarySubset, binaryLabel, hi]

@[simp] theorem binaryLabel_binarySubset (lab : Fin m → Fin 2) :
    binaryLabel (binarySubset lab) = lab := by
  funext i
  by_cases hi : lab i = 0
  · simp [binaryLabel, binarySubset, hi]
  · have h1 : lab i = 1 := by
      apply Fin.ext
      have := (lab i).isLt
      have h0 : (lab i).val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    simp [binaryLabel, binarySubset, h1]

theorem card_binarySubset (lab : Fin m → Fin 2) :
    (binarySubset lab).card = Nat.card {i : Fin m // lab i = 0} := by
  classical
  simp [binarySubset, Nat.card_eq_fintype_card, Fintype.subtype_card]

theorem card_binaryLabel_zero (S : Finset (Fin m)) :
    Nat.card {i : Fin m // binaryLabel S i = 0} = S.card := by
  simpa only [binarySubset_binaryLabel] using (card_binarySubset (binaryLabel S)).symm

theorem card_binaryLabel_one (S : Finset (Fin m)) :
    Nat.card {i : Fin m // binaryLabel S i = 1} = Sᶜ.card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
  congr 1
  ext i
  by_cases hi : i ∈ S <;> simp [binaryLabel, hi]

end Binary

section TwoSource

variable {m₀ m₁ r : ℕ} (hr : 0 < r)
  (B : BlockShape ((m₀ + m₁) * r)) (h₂ : B.length = 2)
  (h₀ : B.size (Fin.cast h₂.symm 0) = m₀ * r)
  (h₁ : B.size (Fin.cast h₂.symm 1) = m₁ * r)

/-- A target-block labeling viewed through the two source labels. -/
def twoSourceBinaryLabel (lab : LabelAssignment B) : Fin (m₀ + m₁) → Fin 2 :=
  fun i => Fin.cast h₂ (lab.val i)

theorem card_twoSourceBinaryLabel (lab : LabelAssignment B) (j : Fin 2) :
    Nat.card {i : Fin (m₀ + m₁) // twoSourceBinaryLabel B h₂ lab i = j} =
      Nat.card {i : Fin (m₀ + m₁) // lab.val i = Fin.cast h₂.symm j} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  constructor
  · intro hi
    exact congrArg (Fin.cast h₂.symm) hi
  · intro hi
    exact congrArg (Fin.cast h₂) hi

include hr h₀ in
theorem card_twoSource_zero (lab : LabelAssignment B) :
    (binarySubset (twoSourceBinaryLabel B h₂ lab)).card = m₀ := by
  rw [card_binarySubset, card_twoSourceBinaryLabel]
  apply Nat.eq_of_mul_eq_mul_right hr
  exact (lab.property (Fin.cast h₂.symm 0)).trans h₀

/-- The source-size constrained labeling associated to a shuffle subset. -/
def assignmentFromSubset (S : {S : Finset (Fin (m₀ + m₁)) // S.card = m₀}) :
    LabelAssignment B := by
  refine ⟨fun i => Fin.cast h₂.symm (binaryLabel S.val i), ?_⟩
  intro j
  have hj : j = Fin.cast h₂.symm 0 ∨ j = Fin.cast h₂.symm 1 := by
    have hjlt : j.val < 2 := h₂ ▸ j.isLt
    by_cases hj0 : j.val = 0
    · exact Or.inl (Fin.ext hj0)
    · exact Or.inr (Fin.ext (by change j.val = 1; omega))
  rcases hj with rfl | rfl
  · have hc : Nat.card {i : Fin (m₀ + m₁) //
        Fin.cast h₂.symm (binaryLabel S.val i) = Fin.cast h₂.symm 0} = S.val.card := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun i =>
        (Fin.cast_injective h₂.symm).eq_iff)), card_binaryLabel_zero]
    rw [hc, S.property, h₀]
  · have hc : Nat.card {i : Fin (m₀ + m₁) //
        Fin.cast h₂.symm (binaryLabel S.val i) = Fin.cast h₂.symm 1} = S.valᶜ.card := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun i =>
        (Fin.cast_injective h₂.symm).eq_iff)), card_binaryLabel_one]
    rw [hc, Finset.card_compl, Fintype.card_fin, S.property, Nat.add_sub_cancel_left, h₁]

/-- Two source-block size constraints are equivalent to a fixed-cardinality subset. -/
def labelAssignmentEquivShuffles :
    LabelAssignment B ≃ {S : Finset (Fin (m₀ + m₁)) // S.card = m₀} where
  toFun lab := ⟨binarySubset (twoSourceBinaryLabel B h₂ lab),
    card_twoSource_zero hr B h₂ h₀ lab⟩
  invFun := assignmentFromSubset B h₂ h₀ h₁
  left_inv lab := by
    apply Subtype.ext
    have hb := binaryLabel_binarySubset (twoSourceBinaryLabel B h₂ lab)
    exact congrArg (fun f => fun i => Fin.cast h₂.symm (f i)) hb
  right_inv S := by
    apply Subtype.ext
    change binarySubset (binaryLabel S.val) = S.val
    exact binarySubset_binaryLabel S.val

/-- Whole uniform target blocks for two source blocks are exactly shuffle subsets. -/
def wholeTargetEquivShuffles :
    WholeTargetRepresentatives hr B ≃ {S : Finset (Fin (m₀ + m₁)) // S.card = m₀} :=
  (wholeTargetEquivLabels hr B).trans (labelAssignmentEquivShuffles hr B h₂ h₀ h₁)

include h₂ h₀ h₁ in
theorem card_wholeTargetRepresentatives :
    Nat.card (WholeTargetRepresentatives hr B) = (m₀ + m₁).choose m₀ := by
  rw [Nat.card_congr (wholeTargetEquivShuffles hr B h₂ h₀ h₁),
    Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

end TwoSource

end Langlands.Classification.ShuffleRefinement
