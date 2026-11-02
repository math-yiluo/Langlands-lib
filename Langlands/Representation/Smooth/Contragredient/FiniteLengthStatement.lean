import Langlands.Representation.Category.Contragredient

/-! # Finite length of the smooth dual of an admissible representation -/

namespace Langlands

universe uG uV

/-- The actual smooth dual preserves finite length on admissible smooth complex
representations when compact open subgroups are cofinal. -/
def SmoothContragredientFiniteLengthStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    CompactOpenCofinal G →
    ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      A.IsAdmissible → A.HasFiniteLength → A.contragredient.HasFiniteLength

end Langlands
