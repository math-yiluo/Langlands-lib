import Langlands.Cohomology.AnalyticEtaleCompactComparison.Reduction
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof

/-! # Compact analytic étale comparison from restricted-injective acyclicity -/

noncomputable section

set_option autoImplicit false

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

open Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

/-- The published geometry discharges the two geometric premises of the
comparison reduction. Restricted-injective compact acyclicity remains an
explicit premise. -/
theorem compactComparison_of_compactAcyclic
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R) :
    AnalyticEtaleCompactComparisonStatement L X h G ρ R :=
  compactComparison_of_openDomains_of_openMap_of_compactAcyclic
    L X h G ρ R (etaleOpenDomainStatement X) (etaleOpenMap K) hacyclic

/-- The canonical compact comparison, packaged as a natural isomorphism
under the remaining compact-acyclicity premise. -/
def compactComparisonIsoOfCompactAcyclic
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R)
    (hT2 : T2Space (localizedSpaceFunctor.obj X))
    (hX : Function.Surjective (pointProjection L X))
    (hcont : IsContinuousAction ρ) (q : ℕ) :
    etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q :=
  compactComparisonIsoOfOpenDomainsOfOpenMapOfCompactAcyclic
    L X h G ρ R (etaleOpenDomainStatement X) (etaleOpenMap K)
    hacyclic hT2 hX hcont q

/-- The forward map is the canonical compact comparison. -/
theorem compactComparisonIsoOfCompactAcyclic_hom
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R)
    (hT2 : T2Space (localizedSpaceFunctor.obj X))
    (hX : Function.Surjective (pointProjection L X))
    (hcont : IsContinuousAction ρ) (q : ℕ) :
    (compactComparisonIsoOfCompactAcyclic L X h G ρ R hacyclic hT2 hX hcont q).hom =
      etaleCompactComparison L ρ h R q := rfl

end Langlands.Cohomology.AnalyticEtaleCompactComparison
