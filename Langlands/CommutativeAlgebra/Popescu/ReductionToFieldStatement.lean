import Langlands.CommutativeAlgebra.Popescu.FieldCaseStatement

/-! # Reduction of Popescu's theorem to a base field -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.8.4 (07F5): if property PT holds for every regular map from a
field to a Noetherian ring, then it holds for every regular map of Noetherian
rings. Property PT is used in its mapping form `HasSmoothFactorizations`. -/
def PopescuReductionToFieldStatement : Prop :=
  PopescuFieldCaseStatement.{u} →
    ∀ (R Λ : Type u) [CommRing R] [CommRing Λ] [IsNoetherianRing R] [IsNoetherianRing Λ]
      [Algebra R Λ], RegularAlgebra R Λ → HasSmoothFactorizations R Λ

end Langlands.CommutativeAlgebra.Popescu
