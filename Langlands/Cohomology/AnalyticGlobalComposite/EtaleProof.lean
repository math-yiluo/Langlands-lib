import Langlands.Cohomology.AnalyticGlobalComposite.SmoothGlobalProof
import Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction

/-! # Berkovich's composite identification for étale G-sheaves -/

noncomputable section

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalComposite

universe w u v uL z

/-- The composite-functor identification for étale G-sheaves, natural in the sheaf. -/
theorem analyticEtaleGlobalComposite
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] :
    AnalyticEtaleGlobalCompositeStatement.{w, u, v, uL, z} X G ρ R := by
  intro _ n
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  let := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  let := etaleGSheafSections_preservesInjectiveObjects.{u, v, uL} ρ R
  exact smoothGlobalComposite R G (etaleGSheafSections.{u, v, uL} ρ R) n

end Langlands.Cohomology.AnalyticGlobalComposite
