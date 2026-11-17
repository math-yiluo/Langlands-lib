import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementReduction
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Sheaf.Equivariant.AnalyticEtalePointLifting
import Langlands.Sheaf.Equivariant.AnalyticEtalePointDetection

/-! # Joint faithfulness of analytic étale field-valued point fibres -/

noncomputable section

universe u v uL

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [NormedAlgebra K L]
  (X : LocalizedCategory.{u, v, v} (K := K))
  (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
  (R : Type (max u (v + 1) uL)) [CommRing R]

/-- On a Hausdorff analytic space with surjective field-point projection,
the actual field-valued étale point fibres jointly detect sheaf morphisms. -/
theorem analyticEtalePointFibersJointlyFaithful :
    AnalyticEtalePointFibersJointlyFaithfulStatement L X h R := by
  intro hT2 hX
  let := hT2
  apply etalePointFibers_jointlyFaithful_of_objectwise_surjective L h
  apply pointProjection_surjective_on_etale_of_openSourceRestriction L h hX
  · exact etaleOpenDomainStatement X
  · intro U V hV
    exact etale_comp (etaleOpenDomainStatement U.left V hV) U.prop

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
