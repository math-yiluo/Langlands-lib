import Langlands.Geometry.Analytic.AnalyticFibreProduct
import Langlands.Geometry.Analytic.EtaleSite

/-! # Statement: étale morphisms are stable under base change -/

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Statement (Berkovich 1993, Corollary 3.3.8): if `f : X → S` is étale, its base change
`X ×_S Y → Y` along any `g : Y → S` is étale, for strong maps of saturated presentations with
Hausdorff spaces. -/
def EtaleBaseChangeStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X Y S : SaturatedAtlasPresentation.{u, u, u} K)
    [T2Space X.presentation.space] [T2Space Y.presentation.space]
    [T2Space S.presentation.space] (f : X ⟶ S) (g : Y ⟶ S),
    etale (localizationFunctor.map f) → etale (localizationFunctor.map (fibreProductSnd f g))

end Langlands.Analytic.SaturatedAtlasPresentation
