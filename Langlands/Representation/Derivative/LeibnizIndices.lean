import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
import Mathlib.Data.Fintype.Sum

/-! Complete index partition for splicing the two mirabolic restriction terms. -/

noncomputable section

namespace Langlands.Derivative

/-- Every feasible right-mixed index is the identical positive-first Leibniz index. -/
def leibnizPositiveIndex {m b d : ℕ} (x : RightMixedDerivativeIndex b m d) :
    LeibnizIndex (m + 1) b d :=
  ⟨x.val, mem_leibnizIndices.mpr
    ⟨rightMixedDerivativeIndices_left_le x.property,
      rightMixedDerivativeIndices_right_le x.property,
      rightMixedDerivativeIndices_sum x.property⟩⟩

/-- The zero-first index exists exactly when the whole order fits in the second rank. -/
def leibnizZeroFirstIndex (m b d : ℕ) (h : d ≤ b) : LeibnizIndex (m + 1) b d :=
  ⟨(0, d), mem_leibnizIndices.mpr ⟨Nat.zero_le _, h, Nat.zero_add _⟩⟩

/-- Partition by positive first order and the optional zero-first order.
This equivalence preserves each underlying pair, including zero pieces. -/
def leibnizIndexSplitEquiv (m b d : ℕ) :
    RightMixedDerivativeIndex b m d ⊕ PLift (d ≤ b) ≃
      LeibnizIndex (m + 1) b d where
  toFun := Sum.elim leibnizPositiveIndex (fun h => leibnizZeroFirstIndex m b d h.down)
  invFun x := if hx : x.val.1 = 0 then
      Sum.inr ⟨by
        have hb := leibnizIndices_right_le x.property
        have hs := leibnizIndices_sum x.property
        omega⟩
    else Sum.inl ⟨x.val, mem_rightMixedDerivativeIndices.mpr
      ⟨by omega, leibnizIndices_left_le x.property,
        leibnizIndices_right_le x.property, leibnizIndices_sum x.property⟩⟩
  left_inv := by
    intro x
    cases x with
    | inl x =>
        have hx : x.val.1 ≠ 0 := by
          have := rightMixedDerivativeIndices_left_pos x.property
          omega
        simp [leibnizPositiveIndex, hx]
    | inr h => rfl
  right_inv := by
    intro x
    dsimp only
    split_ifs with hx
    · apply Subtype.ext
      change (0, d) = x.val
      have hs := leibnizIndices_sum x.property
      exact Prod.ext hx.symm (by omega)
    · rfl

@[simp]
theorem leibnizIndexSplitEquiv_inl (m b d : ℕ)
    (x : RightMixedDerivativeIndex b m d) :
    leibnizIndexSplitEquiv m b d (Sum.inl x) = leibnizPositiveIndex x := rfl

@[simp]
theorem leibnizIndexSplitEquiv_inr (m b d : ℕ) (h : PLift (d ≤ b)) :
    leibnizIndexSplitEquiv m b d (Sum.inr h) = leibnizZeroFirstIndex m b d h.down := rfl

/-- Enumerate the optional zero-first index by a length of either one or zero. -/
def leibnizOptionalIndexEquiv (b d : ℕ) :
    PLift (d ≤ b) ≃ Fin (if d ≤ b then 1 else 0) := by
  by_cases h : d ≤ b
  · rw [ite_eq_left h]
    exact
      { toFun := fun _ => 0
        invFun := fun _ => ⟨h⟩
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  · rw [ite_eq_right h]
    exact
      { toFun := fun x => False.elim (h x.down)
        invFun := Fin.elim0
        left_inv := fun x => False.elim (h x.down)
        right_inv := fun i => Fin.elim0 i }

/-- Exact length of the complete feasible family after the restriction split. -/
theorem leibnizIndices_card_split (m b d : ℕ) :
    (leibnizIndices (m + 1) b d).card =
      (rightMixedDerivativeIndices b m d).card + if d ≤ b then 1 else 0 := by
  have h := Fintype.card_congr (leibnizIndexSplitEquiv m b d).symm
  have hopt := Fintype.card_congr (leibnizOptionalIndexEquiv b d)
  simpa only [Fintype.card_sum, Fintype.card_coe, hopt, Fintype.card_fin] using h

/-- Any complete enumeration of the positive block extends to all feasible
Leibniz indices; the optional last block has exactly the required length. -/
def leibnizSpliceIndexEquiv (m b d : ℕ)
    (e : Fin (rightMixedDerivativeIndices b m d).card ≃ RightMixedDerivativeIndex b m d) :
    Fin ((rightMixedDerivativeIndices b m d).card + if d ≤ b then 1 else 0) ≃
      LeibnizIndex (m + 1) b d :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr e (leibnizOptionalIndexEquiv b d).symm).trans
      (leibnizIndexSplitEquiv m b d))

@[simp]
theorem leibnizSpliceIndexEquiv_castAdd (m b d : ℕ)
    (e : Fin (rightMixedDerivativeIndices b m d).card ≃ RightMixedDerivativeIndex b m d)
    (i : Fin (rightMixedDerivativeIndices b m d).card) :
    leibnizSpliceIndexEquiv m b d e
        (Fin.castAdd (if d ≤ b then 1 else 0) i) =
      leibnizPositiveIndex (e i) := by
  simp [leibnizSpliceIndexEquiv]

@[simp]
theorem leibnizSpliceIndexEquiv_natAdd (m b d : ℕ)
    (e : Fin (rightMixedDerivativeIndices b m d).card ≃ RightMixedDerivativeIndex b m d)
    (i : Fin (if d ≤ b then 1 else 0)) :
    leibnizSpliceIndexEquiv m b d e
        (Fin.natAdd (rightMixedDerivativeIndices b m d).card i) =
      leibnizZeroFirstIndex m b d ((leibnizOptionalIndexEquiv b d).symm i).down := by
  simp [leibnizSpliceIndexEquiv]

end Langlands.Derivative
