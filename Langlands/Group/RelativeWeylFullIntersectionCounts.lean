import Langlands.Group.RelativeWeylCoatomSurvivors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Counting full-source minimal representatives over distinct targets -/

noncomputable section

namespace Langlands.Group.RelativeWeylIndexing

open Classical

universe u v w z

variable {B : Type u} {W : Type v} [Group W] [Fintype B] [Fintype W]
  {C : CoxeterMatrix B} (cs : CoxeterSystem C W)

/-- The minimal representatives with full source intersection for one target. -/
def fullIntersectionRepresentatives (J I : Finset B) : Finset W :=
  (minimalReps cs J I).filter (fun w => intersectionSubset cs J I w = I)

@[simp]
theorem mem_fullIntersectionRepresentatives (J I : Finset B) (w : W) :
    w ∈ fullIntersectionRepresentatives cs J I ↔
      IsMinimal cs J I w ∧ intersectionSubset cs J I w = I := by
  simp [fullIntersectionRepresentatives, mem_minimalReps]

/-- A bijective enumeration of the minimal representatives counts each full
source intersection exactly once. The values can lie in any additive monoid
with its natural-number casts. -/
theorem sum_fullIntersectionIndicators {R : Type z} [AddCommMonoidWithOne R]
    (J I : Finset B) {n : ℕ} (e : Fin n ≃ (minimalReps cs J I)) :
    (∑ q, if intersectionSubset cs J I (e q).val = I then (1 : R) else 0) =
      ((fullIntersectionRepresentatives cs J I).card : R) := by
  calc
    _ = ∑ w : minimalReps cs J I,
        if intersectionSubset cs J I w.val = I then (1 : R) else 0 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [Finset.sum_coe_sort (s := minimalReps cs J I)
        (f := fun w : W => if intersectionSubset cs J I w = I then (1 : R) else 0)]
      simp [fullIntersectionRepresentatives]

/-- Distinct target labels of the source cardinality count no more than all
equal-rank full-intersection pairs. -/
theorem sum_card_fullIntersectionRepresentatives_le
    {A : Type w} [Fintype A] (I : Finset B) (target : A → Finset B)
    (htarget : Function.Injective target)
    (hcard : ∀ a, (target a).card = I.card) :
    (∑ a, (fullIntersectionRepresentatives cs (target a) I).card) ≤
      (fullIntersectionPairs cs I).card := by
  let S : Finset (Σ _ : A, W) :=
    Finset.univ.sigma fun a => fullIntersectionRepresentatives cs (target a) I
  let f : (Σ _ : A, W) → Finset B × W := fun p => (target p.1, p.2)
  have hmap : Set.MapsTo f S (fullIntersectionPairs cs I) := by
    rintro ⟨a, w⟩ hp
    have hw := (mem_fullIntersectionRepresentatives cs (target a) I w).mp
      (Finset.mem_sigma.mp hp).2
    change (target a, w) ∈ fullIntersectionPairs cs I
    simp only [fullIntersectionPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcard a, hw⟩
  have hinj : (S : Set (Σ _ : A, W)).InjOn f := by
    rintro ⟨a, w⟩ _ ⟨a', w'⟩ _ h
    have ha : a = a' := htarget (congrArg Prod.fst h)
    subst a'
    have hw : w = w' := congrArg Prod.snd h
    subst w'
    rfl
  calc
    _ = S.card := by simp [S, Finset.card_sigma]
    _ ≤ _ := Finset.card_le_card_of_injOn f hmap hinj

end Langlands.Group.RelativeWeylIndexing
