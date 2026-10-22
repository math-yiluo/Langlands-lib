import Langlands.Cohomology.Tate.ShiftDefinitions

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Induction on actual Tate classes through the proved scalar-split shifts. -/
lemma tateClass_shift_induction
    (P : (A : Rep.{u} R G) → (n : ℤ) → tateCohomology A n → Prop)
    (hz : ∀ A x, P A 0 x)
    (hu : ∀ A n x, P (shiftUp A) n x →
      P A (n + 1) ((shiftUpIso A n).hom x))
    (hd : ∀ A n x, P (shiftDown A) (n + 1) ((shiftDownIso A n).hom x) → P A n x)
    (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) : P A n x := by
  have hpos : ∀ n : ℕ, ∀ A x, P A n x := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      intro A x
      obtain ⟨y, rfl⟩ := (shiftUpIso A n).toLinearEquiv.surjective x
      exact hu A n y (ih (shiftUp A) y)
  have hneg : ∀ n : ℕ, ∀ A x, P A (-(n : ℤ)) x := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      intro A x
      apply hd A (-((n + 1 : ℕ) : ℤ)) x
      have hn : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      have hh : ∀ y, P (shiftDown A) (-((n + 1 : ℕ) : ℤ) + 1) y := by
        rw [hn]
        exact ih (shiftDown A)
      exact hh _
  cases n with
  | ofNat n => exact hpos n A x
  | negSucc n => exact hneg (n + 1) A x

end Langlands.Tate
