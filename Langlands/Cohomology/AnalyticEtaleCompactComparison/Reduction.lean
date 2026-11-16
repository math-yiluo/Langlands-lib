import Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement
import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Statement
import Langlands.Geometry.Analytic.EtaleOpenMap.Statement
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactDerivedComparison
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactGlobal
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactLocal

/-! # Exact remaining inputs to the compact analytic étale comparison -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
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

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

/-- Given the point axioms `h`, compact acyclicity implies ordinary acyclicity
on compact spaces through the actual compact/global cohomology isomorphism. -/
theorem globalAcyclic_of_compactAcyclic
    (hcompact : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R) :
    AnalyticEtaleRestrictedInjectiveGlobalAcyclicStatement L X G ρ R := by
  intro hT2 hcomp hX hcont I hI q
  let := hcomp
  exact (isZero_etaleCompactCohomology_iff_of_compactSpace L h R hX (q + 1)
    ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)).mp
      (hcompact hT2 hX hcont I hI q)

/-- With the supplied point axioms, the combined acyclicity prerequisite is
equivalent to its compact-support component. -/
theorem acyclic_iff_compactAcyclic :
    AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R ↔
      AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R := by
  exact ⟨And.left, fun hc => ⟨hc, globalAcyclic_of_compactAcyclic L X h G ρ R hc⟩⟩

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

open Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

/-- Open-domain étaleness, étale openness and compact acyclicity of restricted
injectives imply the exact published compact comparison statement. Each of
these three inputs is an explicit premise, not a theorem asserted here. -/
theorem compactComparison_of_openDomains_of_openMap_of_compactAcyclic
    (hdomains : EtaleOpenDomainStatement X)
    (hopen : EtaleOpenMapStatement.{u, v} K)
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R) :
    AnalyticEtaleCompactComparisonStatement L X h G ρ R := by
  intro hT2 hX hcont q
  let := hT2
  have hlift := etalePointLifting_of_openDomains L h hdomains
  have hopen' : ∀ U : EtaleSite X, IsOpenMap (localizedSpaceFunctor.map U.hom) :=
    fun U => hopen U.hom U.prop
  have hzero := isIso_etaleCompactInclusion (R := R) L h ρ hlift hX hopen'
  refine isIso_etaleCompactComparison_of_injective_acyclic L ρ h R hzero ?_ q
  intro I hI r
  exact hacyclic hT2 hX hcont I hI r

/-- Package the canonical compact comparison as a natural isomorphism, with
the remaining geometry and compact-acyclicity inputs supplied explicitly. -/
def compactComparisonIsoOfOpenDomainsOfOpenMapOfCompactAcyclic
    (hdomains : EtaleOpenDomainStatement X)
    (hopen : EtaleOpenMapStatement.{u, v} K)
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R)
    (hT2 : T2Space (localizedSpaceFunctor.obj X))
    (hX : Function.Surjective (pointProjection L X))
    (hcont : IsContinuousAction ρ) (q : ℕ) :
    etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q :=
  haveI := compactComparison_of_openDomains_of_openMap_of_compactAcyclic
    L X h G ρ R hdomains hopen hacyclic hT2 hX hcont q
  asIso (etaleCompactComparison L ρ h R q)

/-- The conditional natural isomorphism has the canonical comparison as its
forward transformation. -/
theorem compactComparisonIsoOfOpenDomainsOfOpenMapOfCompactAcyclic_hom
    (hdomains : EtaleOpenDomainStatement X)
    (hopen : EtaleOpenMapStatement.{u, v} K)
    (hacyclic : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R)
    (hT2 : T2Space (localizedSpaceFunctor.obj X))
    (hX : Function.Surjective (pointProjection L X))
    (hcont : IsContinuousAction ρ) (q : ℕ) :
    (compactComparisonIsoOfOpenDomainsOfOpenMapOfCompactAcyclic
      L X h G ρ R hdomains hopen hacyclic hT2 hX hcont q).hom =
        etaleCompactComparison L ρ h R q := rfl

end Langlands.Cohomology.AnalyticEtaleCompactComparison
