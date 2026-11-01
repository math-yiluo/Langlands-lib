import Langlands.Representation.Aubert.RefinementCuts

/-! The signed nested-refinement sum cancels to the shape without cuts. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric
open scoped BigOperators

variable {n : ℕ}

private theorem sign_eq_cut_card (B : BlockShape n) :
    (-1 : ℤ) ^ (n - B.length) =
      (-1 : ℤ) ^ (n - 1) * (-1 : ℤ) ^ B.cuts.card := by
  have hc : B.uncuts.card + B.cuts.card = n - 1 := by
    rw [BlockShape.uncuts,
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)]
    simp
  have hp : (-1 : ℤ) ^ (n - 1) =
      (-1 : ℤ) ^ B.uncuts.card * (-1 : ℤ) ^ B.cuts.card := by
    rw [← pow_add, hc]
  rw [BlockShape.sign_eq_pow_uncuts_card, hp, mul_assoc, ← mul_pow]
  simp

private theorem sum_subtype_as_ite {ι M : Type*} [Fintype ι]
    [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] (g : ι → M) :
    (∑ x : {x // p x}, g x.val) = ∑ x : ι, if p x then g x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) g).symm

/-- The coefficient of a fixed flattened shape after exchanging the two sums. -/
def refinementSquareCoefficient (C : BlockShape n) : ℤ :=
  letI : Fintype (BlockShape n) := Fintype.ofFinite _
  (∑ B : {B : BlockShape n // B.cuts ⊆ C.cuts}, (-1 : ℤ) ^ (n - B.val.length)) *
    (-1 : ℤ) ^ (n - C.length)

/-- Every coefficient vanishes except that of the shape without cuts. -/
theorem refinementSquareCoefficient_eq (C : BlockShape n) :
    refinementSquareCoefficient C = if C.cuts = ∅ then 1 else 0 := by
  classical
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  let e : {B : BlockShape n // B.cuts ⊆ C.cuts} ≃
      {s : Finset (Fin (n - 1)) // s ⊆ C.cuts} :=
    Equiv.subtypeEquiv (BlockShape.cutEquiv n) (fun _ => Iff.rfl)
  have hs :
      (∑ B : {B : BlockShape n // B.cuts ⊆ C.cuts},
        (-1 : ℤ) ^ (n - B.val.length)) =
      (-1 : ℤ) ^ (n - 1) *
        (if C.cuts = ∅ then 1 else 0) := by
    calc
      _ = ∑ s : {s : Finset (Fin (n - 1)) // s ⊆ C.cuts},
          (-1 : ℤ) ^ (n - 1) * (-1 : ℤ) ^ s.val.card := by
        apply Fintype.sum_equiv e
        intro B
        exact sign_eq_cut_card B.val
      _ = (-1 : ℤ) ^ (n - 1) *
          ∑ s : {s : Finset (Fin (n - 1)) // s ⊆ C.cuts},
            (-1 : ℤ) ^ s.val.card := by rw [Finset.mul_sum]
      _ = (-1 : ℤ) ^ (n - 1) *
          ∑ s ∈ C.cuts.powerset, (-1 : ℤ) ^ s.card := by
        congr 1
        exact (Finset.sum_subtype C.cuts.powerset
          (fun s => Finset.mem_powerset) (fun s => (-1 : ℤ) ^ s.card)).symm
      _ = _ := by rw [Finset.sum_powerset_neg_one_pow_card]
  change _ * _ = _
  rw [hs, sign_eq_cut_card C]
  by_cases hC : C.cuts = ∅
  · simp [hC, ← mul_pow]
  · simp [hC]

/-- The generic double sum obtained by expanding the square after commutation
and actual transitivity, with the original unadjusted signs. -/
def refinementAlternatingSum {M : Type*} [AddCommGroup M]
    (f : BlockShape n → M) : M :=
  letI : Fintype (BlockShape n) := Fintype.ofFinite _
  letI (B : BlockShape n) : Fintype (BlockRefinement B) := Fintype.ofFinite _
  ∑ B : BlockShape n, ∑ S : BlockRefinement B,
    ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - (B.flatten S).length)) •
      f (B.flatten S)

/-- Nested alternating refinements cancel to the coarsest shape, in all ranks. -/
theorem refinementAlternatingSum_eq {M : Type*} [AddCommGroup M]
    (f : BlockShape n → M) :
    refinementAlternatingSum f = f ((BlockShape.cutEquiv n).symm ∅) := by
  classical
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  let (B : BlockShape n) : Fintype (BlockRefinement B) := Fintype.ofFinite _
  change (∑ B : BlockShape n, ∑ S : BlockRefinement B, _) = _
  calc
    _ = ∑ B : BlockShape n,
        ∑ C : {C : BlockShape n // B.cuts ⊆ C.cuts},
          ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - C.val.length)) • f C.val := by
      apply Finset.sum_congr rfl
      intro B _
      exact Fintype.sum_equiv (refinementCutsEquiv B) _ _ (fun S => rfl)
    _ = ∑ B : BlockShape n, ∑ C : BlockShape n,
        if B.cuts ⊆ C.cuts then
          ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - C.length)) • f C else 0 := by
      apply Finset.sum_congr rfl
      intro B _
      exact sum_subtype_as_ite (fun C : BlockShape n => B.cuts ⊆ C.cuts)
        (fun C => ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - C.length)) • f C)
    _ = ∑ C : BlockShape n, ∑ B : BlockShape n,
        if B.cuts ⊆ C.cuts then
          ((-1 : ℤ) ^ (n - B.length) * (-1 : ℤ) ^ (n - C.length)) • f C else 0 :=
      Finset.sum_comm
    _ = ∑ C : BlockShape n, refinementSquareCoefficient C • f C := by
      apply Finset.sum_congr rfl
      intro C _
      rw [← sum_subtype_as_ite]
      change (∑ B : {B : BlockShape n // B.cuts ⊆ C.cuts},
        ((-1 : ℤ) ^ (n - B.val.length) * (-1 : ℤ) ^ (n - C.length)) • f C) = _
      change _ = ((∑ B : {B : BlockShape n // B.cuts ⊆ C.cuts},
        (-1 : ℤ) ^ (n - B.val.length)) * (-1 : ℤ) ^ (n - C.length)) • f C
      rw [Finset.sum_mul, Finset.sum_smul]
    _ = f ((BlockShape.cutEquiv n).symm ∅) := by
      rw [Finset.sum_eq_single ((BlockShape.cutEquiv n).symm ∅)]
      · rw [refinementSquareCoefficient_eq, BlockShape.cuts_cutEquiv_symm]
        simp
      · intro C _ hC
        rw [refinementSquareCoefficient_eq, ite_eq_right]
        · exact zero_smul _ _
        · intro h
          apply hC
          apply BlockShape.cuts_injective
          simpa using h
      · simp

end Langlands.Aubert
