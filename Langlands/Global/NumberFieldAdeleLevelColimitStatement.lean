import Langlands.Global.NumberFieldAdeleLevelDiagram

/-! # Categorical colimits of the actual full number-field adelic level cocones -/

universe u

open CategoryTheory Limits

namespace Langlands.Global

/-- The actual full adele ring is the colimit in topological rings and in rings. -/
def NumberFieldAdeleLevelColimitStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    Nonempty (IsColimit (numberFieldAdeleLevelCocone K)) ∧
      Nonempty (IsColimit (numberFieldAdeleLevelRingCocone K))

end Langlands.Global
