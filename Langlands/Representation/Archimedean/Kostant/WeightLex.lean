import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.Weight

/-!
# Weighted lexicographic monomial orders

For a linearly ordered type of variables `σ` with `WellFoundedGT σ` and a weight
`w : σ → ℕ`, `weightLex w` is the monomial order on `σ →₀ ℕ` that compares the weights
`Finsupp.weight w` first and breaks ties with the lexicographic order `Lex (σ →₀ ℕ)`.
For the constant weight `1` this is Mathlib's `MonomialOrder.degLex`; the construction
follows `Mathlib/Data/Finsupp/MonomialOrder/DegLex.lean` with the weight in place of the
degree.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

open Finsupp

/-- Type synonym of `σ →₀ ℕ` that carries the weighted lexicographic order for `w`. -/
def WeightLex {σ : Type*} (_w : σ → ℕ) : Type _ := σ →₀ ℕ

namespace WeightLex

variable {σ : Type*} (w : σ → ℕ)

instance : AddCommMonoid (WeightLex w) := inferInstanceAs (AddCommMonoid (σ →₀ ℕ))

/-- The identity of `σ →₀ ℕ`, viewed as an additive equivalence onto the synonym. -/
def toWL : (σ →₀ ℕ) ≃+ WeightLex w where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The comparison key of an element: its weight, then its lexicographic class. -/
def key [LinearOrder σ] (f : WeightLex w) : Lex (ℕ × Lex (σ →₀ ℕ)) :=
  toLex (Finsupp.weight w ((toWL w).symm f), toLex ((toWL w).symm f))

variable [LinearOrder σ]

theorem key_injective : Function.Injective (key w) := by
  intro f g h
  have h2 := congrArg (fun x => ofLex (ofLex x).2) h
  simpa [key] using h2

instance : LinearOrder (WeightLex w) := LinearOrder.lift' (key w) (key_injective w)

theorem lt_def {f g : WeightLex w} : f < g ↔ key w f < key w g := Iff.rfl

theorem le_def {f g : WeightLex w} : f ≤ g ↔ key w f ≤ key w g := Iff.rfl

theorem toWL_lt_iff {a b : σ →₀ ℕ} :
    toWL w a < toWL w b ↔
      Finsupp.weight w a < Finsupp.weight w b ∨
        (Finsupp.weight w a = Finsupp.weight w b ∧ toLex a < toLex b) := by
  rw [lt_def]
  exact Prod.Lex.toLex_lt_toLex

theorem toWL_le_iff {a b : σ →₀ ℕ} :
    toWL w a ≤ toWL w b ↔
      Finsupp.weight w a < Finsupp.weight w b ∨
        (Finsupp.weight w a = Finsupp.weight w b ∧ toLex a ≤ toLex b) := by
  rw [le_def]
  exact Prod.Lex.toLex_le_toLex

instance : IsOrderedCancelAddMonoid (WeightLex w) where
  add_le_add_left a b h c := by
    obtain ⟨a, rfl⟩ := (toWL w).surjective a
    obtain ⟨b, rfl⟩ := (toWL w).surjective b
    obtain ⟨c, rfl⟩ := (toWL w).surjective c
    rw [← map_add, ← map_add, toWL_le_iff] at *
    simpa [map_add, toLex_add] using h
  le_of_add_le_add_left a b c h := by
    obtain ⟨a, rfl⟩ := (toWL w).surjective a
    obtain ⟨b, rfl⟩ := (toWL w).surjective b
    obtain ⟨c, rfl⟩ := (toWL w).surjective c
    rw [← map_add, ← map_add, toWL_le_iff] at h
    rw [toWL_le_iff]
    simpa [map_add, toLex_add] using h

instance [WellFoundedGT σ] : WellFoundedLT (WeightLex w) :=
  InvImage.wf (key w) wellFounded_lt

end WeightLex

open WeightLex

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- The weighted lexicographic monomial order: compare `Finsupp.weight w` first, then the
lexicographic order of `σ →₀ ℕ`. -/
def weightLex (w : σ → ℕ) : MonomialOrder σ where
  syn := WeightLex w
  toSyn := toWL w
  toSyn_monotone a b h := by
    rw [toWL_le_iff]
    have hw : Finsupp.weight w a ≤ Finsupp.weight w b := by
      rw [← add_tsub_cancel_of_le h, map_add]
      exact Nat.le_add_right _ _
    rcases hw.lt_or_eq with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, toLex_monotone h⟩

open scoped MonomialOrder

theorem weightLex_lt_iff (w : σ → ℕ) {a b : σ →₀ ℕ} :
    a ≺[weightLex w] b ↔
      Finsupp.weight w a < Finsupp.weight w b ∨
        (Finsupp.weight w a = Finsupp.weight w b ∧ toLex a < toLex b) :=
  toWL_lt_iff w

end Langlands.Archimedean.Kostant
