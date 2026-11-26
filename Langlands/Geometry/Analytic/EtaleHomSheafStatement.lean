import Langlands.Geometry.Analytic.EtaleSite

/-! # Descent of analytic morphisms for the étale topology -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Morphisms to any analytic space satisfy existence and uniqueness of descent on the
étale site of every analytic space: `U ↦ Hom(U, T)` is a sheaf for `etaleTopology X`
(Berkovich 1993, §4.1; Conrad–Temkin 2009, Theorem 4.1.2). -/
def EtaleHomSheafStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X T : LocalizedCategory.{u, v, v} (K := K)),
    Presieve.IsSheaf (etaleTopology X)
      ((MorphismProperty.Over.forget _ _ X ⋙ Over.forget X).op ⋙ yoneda.obj T)

end Langlands.Analytic.SaturatedAtlasPresentation
