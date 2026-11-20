import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Étaleness under open-source restriction -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Restricting the source of a localized étale morphism to an open subset
preserves étaleness. -/
def EtaleOpenSourceRestrictionStatement
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ ⦃U X : LocalizedCategory.{u, v, v} (K := K)⦄ (f : U ⟶ X),
    etale f → ∀ (V : Set (localizedSpaceFunctor.obj U)) (hV : IsOpen V),
      etale (domainι U ((presentationOf U).openDomain V hV) ≫ f)

end Langlands.Analytic.SaturatedAtlasPresentation
