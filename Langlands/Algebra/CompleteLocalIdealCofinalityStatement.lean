import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Adic cofinality of a separated descending sequence of local ideals: statement -/

universe u

namespace Langlands.Algebra

/-- A separated decreasing sequence of ideals in a complete Noetherian local ring
is eventually contained in every power of the actual maximal ideal. -/
def CompleteLocalIdealCofinalityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (J : ℕ → Ideal R),
    Antitone J → (⨅ n, J n) = ⊥ →
      ∀ a : ℕ, ∃ n : ℕ, J n ≤ IsLocalRing.maximalIdeal R ^ a

end Langlands.Algebra
