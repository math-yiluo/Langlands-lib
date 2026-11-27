import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Langlands.Geometry.Analytic.QuasiEtaleSite

/-! # Étale and quasi-étale morphisms under extension of the ground field -/

universe u u' v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory AffinoidAtlasPresentation.GroundFieldExtension

/-- Extending a complete nonarchimedean ground field preserves the étale and
quasi-étale morphism properties in the localized analytic categories. -/
def GroundFieldExtensionEtaleStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
    {Y X : LocalizedCategory.{u, v, v} (K := K)} (f : Y ⟶ X),
    (etale f → etale ((localizedFunctor K L).map f)) ∧
      (quasiEtale f → quasiEtale ((localizedFunctor K L).map f))

end Langlands.Analytic.SaturatedAtlasPresentation
