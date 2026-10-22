import Langlands.Cohomology.Tate.ShiftDefinitions
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The ordinary connecting map of the canonical coinduced embedding sequence. -/
abbrev ordinaryShiftUpDelta (A : Rep.{u} R G) (n : ℕ) :
    groupCohomology (shiftUp A) n ⟶ groupCohomology A (n + 1) :=
  groupCohomology.δ (shiftUpSequence_shortExact A) n (n + 1) rfl

lemma coinduced_groupCohomology_isZero (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (coinduced A) n) :=
  (coinduced_tate_isZero A n).of_iso
    ((TateCohomology.isoGroupCohomology n).app (coinduced A)).symm

/-- Every positive ordinary class lifts through this actual connecting map. -/
lemma ordinaryShiftUpDelta_surjective (A : Rep.{u} R G) (n : ℕ) :
    Function.Surjective (ordinaryShiftUpDelta A n) := by
  have := groupCohomology.epi_δ_of_isZero (shiftUpSequence_shortExact A) n
    (coinduced_groupCohomology_isZero A (n + 1))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Positive ordinary dimension shifting; degree zero only has the surjection above. -/
def ordinaryShiftUpIso (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    groupCohomology (shiftUp A) n ≅ groupCohomology A (n + 1) := by
  have := groupCohomology.isIso_δ_of_isZero (shiftUpSequence_shortExact A) n
    (coinduced_groupCohomology_isZero A n)
    (coinduced_groupCohomology_isZero A (n + 1))
  exact asIso (ordinaryShiftUpDelta A n)

@[simp]
lemma ordinaryShiftUpIso_hom (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    (ordinaryShiftUpIso A n).hom = ordinaryShiftUpDelta A n := rfl

/-- Induction on actual ordinary classes using the coinduced embedding sequence. -/
lemma ordinaryClass_shift_induction
    (P : (A : Rep.{u} R G) → (n : ℕ) → groupCohomology A n → Prop)
    (hz : ∀ A a, P A 0 ((groupCohomology.H0Iso A).inv a))
    (hu : ∀ A n x, P (shiftUp A) n x →
      P A (n + 1) (ordinaryShiftUpDelta A n x))
    (A : Rep.{u} R G) (n : ℕ) (x : groupCohomology A n) : P A n x := by
  induction n generalizing A with
  | zero =>
      obtain ⟨a, rfl⟩ := (groupCohomology.H0Iso A).symm.toLinearEquiv.surjective x
      exact hz A a
  | succ n ih =>
      obtain ⟨y, rfl⟩ := ordinaryShiftUpDelta_surjective A n x
      exact hu A n y (ih (shiftUp A) y)

/-- Two-variable class induction, first reducing the second degree, then the first. -/
lemma ordinaryClasses_shift_induction
    (P : (A B : Rep.{u} R G) → (p q : ℕ) →
      groupCohomology A p → groupCohomology B q → Prop)
    (hz : ∀ A B a b, P A B 0 0
      ((groupCohomology.H0Iso A).inv a) ((groupCohomology.H0Iso B).inv b))
    (hl : ∀ A B p a b, P (shiftUp A) B p 0 a b →
      P A B (p + 1) 0 (ordinaryShiftUpDelta A p a) b)
    (hr : ∀ A B p q a b, P A (shiftUp B) p q a b →
      P A B p (q + 1) a (ordinaryShiftUpDelta B q b))
    (A B : Rep.{u} R G) (p q : ℕ)
    (a : groupCohomology A p) (b : groupCohomology B q) : P A B p q a b := by
  induction q generalizing B with
  | zero =>
      obtain ⟨b, rfl⟩ := (groupCohomology.H0Iso B).symm.toLinearEquiv.surjective b
      exact ordinaryClass_shift_induction
        (fun A p a => P A B p 0 a ((groupCohomology.H0Iso B).inv b))
        (fun A a => hz A B a b)
        (fun A p a ha => hl A B p a _ ha) A p a
  | succ q ih =>
      obtain ⟨y, rfl⟩ := ordinaryShiftUpDelta_surjective B q b
      exact hr A B p q a y (ih (shiftUp B) y)

end Langlands.Tate
