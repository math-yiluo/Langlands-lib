import Langlands.Cohomology.AnalyticGlobalComposite.SmoothGlobalProof
import Langlands.Sheaf.Equivariant.AnalyticConstantAdjunction

/-! # Berkovich's composite comparison for quasi-étale `G`-sheaves -/

noncomputable section

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalComposite

universe w u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (X : LocalizedCategory.{u, v, v} (K := K))
  (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
  [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
  (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The natural composite identification of Berkovich §1.2 for quasi-étale `G`-sheaves,
with the full universe and instance scope of the published statement. -/
theorem analyticQuasiEtaleGlobalComposite :
    AnalyticQuasiEtaleGlobalCompositeStatement.{w, u, v, uL, z} X G ρ R := by
  intro _ n
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  let := HasDerivedCategory.standard
    (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  have := quasiEtaleGSheafSections_preservesInjectiveObjects.{u, v, uL} ρ R
  exact smoothGlobalComposite R G (quasiEtaleGSheafSections.{u, v, uL} ρ R) n

end Langlands.Cohomology.AnalyticGlobalComposite
