import Langlands.Geometry.Analytic.AnalyticFibreProduct
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Statement: the glued fibre product is a fibre product of analytic spaces -/

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Statement (Berkovich 1993, Proposition 1.4.1): for strong maps `f : X → S` and
`g : Y → S` of saturated presentations with Hausdorff spaces, the glued fibre product with
its two projections is a pullback of `f` and `g` in the localized category of analytic
spaces. -/
def FibreProductPullbackStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X Y S : SaturatedAtlasPresentation.{u, u, u} K)
    [T2Space X.presentation.space] [T2Space Y.presentation.space]
    [T2Space S.presentation.space] (f : X ⟶ S) (g : Y ⟶ S),
    IsPullback (localizationFunctor.map (fibreProductFst f g))
      (localizationFunctor.map (fibreProductSnd f g))
      (localizationFunctor.map f) (localizationFunctor.map g)

end Langlands.Analytic.SaturatedAtlasPresentation
