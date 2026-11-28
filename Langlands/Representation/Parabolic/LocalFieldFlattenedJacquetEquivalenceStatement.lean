import Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientStatement

/-! Actual iterated and flattened normalized Jacquet modules over a local field. -/

namespace Langlands.AllField.Parabolic

open Langlands.GeneralLinear Langlands.Geometric

universe uF uV

/-- Flattened normalized Jacquet restriction is equivariantly equivalent
to iterated restriction, with the double quotient map on representatives. -/
def LocalFieldFlattenedJacquetEquivalenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) (B : BlockShape n)
    (S : BlockRefinement B) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V),
    Nonempty {e : (T.normalizedJacquet (B.flatten S) ρ).Equiv
        ((T.normalizedRefinedJacquet B S (T.normalizedJacquet B ρ)).comp
          (flattenedLeviEquiv F B S).toMonoidHom) //
      ∀ v, e ((B.flatten S).jacquetMk ρ v) =
        refinedJacquetMk B S (T.normalizedJacquet B ρ) (B.jacquetMk ρ v)}

end Langlands.AllField.Parabolic
