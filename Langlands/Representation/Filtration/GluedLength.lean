import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Filtration.SingleSurvivingGrade

/-! # Composition length of an actual glued functor -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uK uG uV uC vC

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} k G} {n : ℕ} {pieces : Fin n → C ⥤ Rep.{uV} k G}

/-- The actual composition-length formula for a supplied finite gluing. -/
def GluedLengthFormulaStatement (F : C ⥤ Rep.{uV} k G)
    (pieces : Fin n → C ⥤ Rep.{uV} k G) : Prop :=
  IsGluedFrom F pieces → ∀ X : C,
    repLength (F.obj X).ρ = ∑ i : Fin n, repLength ((pieces i).obj X).ρ

/-- Evaluation of a genuine glued filtration computes actual composition length,
including infinite length, as the sum of the lengths of all its pieces. -/
theorem IsGluedFrom.repLength_eq_sum (h : IsGluedFrom F pieces) (X : C) :
    repLength (F.obj X).ρ = ∑ i : Fin n, repLength ((pieces i).obj X).ρ := by
  classical
  obtain ⟨e, s, hs⟩ := h
  rw [repLength_eq_sum_of_filtration (s.atObject X)]
  calc
    _ = ∑ i : Fin n, repLength ((pieces (e i)).obj X).ρ := by
      apply Finset.sum_congr rfl
      intro i _
      exact repLength_congr (Representation.equivOfIso ((Classical.choice (hs i)).app X))
    _ = ∑ i : Fin n, repLength ((pieces i).obj X).ρ :=
      Equiv.sum_comp e (fun i => repLength ((pieces i).obj X).ρ)

/-- Every actual gluing satisfies the formula proposition. -/
theorem gluedLengthFormula : GluedLengthFormulaStatement F pieces :=
  fun h X => h.repLength_eq_sum X

/-- Zero pieces can be discarded without changing the total composition length. -/
theorem IsGluedFrom.repLength_eq_sum_on (h : IsGluedFrom F pieces) (X : C)
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Subsingleton ((pieces i).obj X)) :
    repLength (F.obj X).ρ = ∑ i ∈ S, repLength ((pieces i).obj X).ρ := by
  classical
  rw [h.repLength_eq_sum X]
  symm
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi =>
    repLength_eq_zero_iff.mpr (hzero i hi))

/-- If the remaining pieces each have length at most one, their number bounds
the length of the glued object. No finite-length premise is supplied. -/
theorem IsGluedFrom.repLength_le_card (h : IsGluedFrom F pieces) (X : C)
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Subsingleton ((pieces i).obj X))
    (hone : ∀ i ∈ S, repLength ((pieces i).obj X).ρ ≤ 1) :
    repLength (F.obj X).ρ ≤ (S.card : ℕ∞) := by
  classical
  rw [h.repLength_eq_sum_on X S hzero]
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℕ∞) := Finset.sum_le_sum hone
    _ = (S.card : ℕ∞) := by simp

/-- Irreducible surviving pieces count with their actual multiplicity. -/
theorem IsGluedFrom.repLength_eq_card (h : IsGluedFrom F pieces) (X : C)
    (S : Finset (Fin n)) (hzero : ∀ i, i ∉ S → Subsingleton ((pieces i).obj X))
    (hirr : ∀ i ∈ S, ((pieces i).obj X).ρ.IsIrreducible) :
    repLength (F.obj X).ρ = (S.card : ℕ∞) := by
  classical
  rw [h.repLength_eq_sum_on X S hzero]
  calc
    _ = ∑ _i ∈ S, (1 : ℕ∞) :=
      Finset.sum_congr rfl (fun i hi => repLength_eq_one_iff.mpr (hirr i hi))
    _ = (S.card : ℕ∞) := by simp

end Langlands
