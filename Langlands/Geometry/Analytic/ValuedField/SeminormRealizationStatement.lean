import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Complete-field realization of an ultrametric multiplicative seminorm -/

universe u

namespace Langlands.Analytic

/-- An ultrametric multiplicative seminorm is realized in one complete
ultrametric normed field in the universe of its source ring. -/
def SeminormRealizationStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (q : MulRingSeminorm A),
    IsNonarchimedean q →
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L)
      (_ : CompleteSpace L) (f : A →+* L), ∀ a, ‖f a‖ = q a

end Langlands.Analytic
