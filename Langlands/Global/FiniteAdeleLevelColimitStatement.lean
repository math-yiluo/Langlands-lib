import Langlands.Global.FiniteAdeleLevelDiagram

/-! # Categorical colimits of the actual finite-adelic level cocones -/

universe u

open IsDedekindDomain CategoryTheory Limits

namespace Langlands.Global

/-- The actual finite adele ring is the colimit in both topological rings and rings. -/
def FiniteAdeleLevelColimitStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K],
    Nonempty (IsColimit (finiteAdeleLevelCocone R K)) ∧
      Nonempty (IsColimit (finiteAdeleLevelRingCocone R K))

end Langlands.Global
