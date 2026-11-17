import Langlands.Sheaf.Equivariant.TwistedGodementPointProduct
import Langlands.Sheaf.Equivariant.TwistedPointProductAcyclic
import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementReduction

/-! # The actual analytic Godement term and injective coefficient diagrams -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The actual restricted smooth point product on independent analytic point coefficients. -/
def etaleCoefficientRestrictedSmoothPointProductFunctor :
    (Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
      ModuleCat.{max u (v + 1) uL} R) ⥤
        Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  coefficientRestrictedSmoothPointProductFunctor ρ (etaleTopology X)
    (distinguishedLiftSystem ρ) (etaleGodementPoints L h) R

/-- The actual fibers used as coefficients of the analytic Godement construction. -/
def etaleGodementCoefficientFunctor :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      (Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
        ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  smoothGodementCoefficientFunctor ρ (etaleTopology X)
    (distinguishedLiftSystem ρ) (etaleGodementPoints L h) R

/-- Natural identification of the existing restricted analytic Godement term with its
actual independent-coefficient point product. -/
def etaleRestrictedGodementPointProductIso :
    etaleGodementZeroFunctor L ρ h R ⋙ etaleGSheafRestriction.{u, v, uL} ρ R ≅
      etaleGodementCoefficientFunctor L ρ h R ⋙
        etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  restrictedSmoothGodementPointProductIso ρ (etaleTopology X)
    (distinguishedLiftSystem ρ) (etaleGodementPoints L h) R

/-- The generic coefficient reduction specializes to actual analytic compact cohomology.
The remaining injective-coefficient vanishing is an explicit hypothesis. -/
theorem isZero_etaleCompactCohomology_coefficientRestrictedSmoothPointProduct_of_injective
    (hΓ : ∀ N : Discrete
        (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
          ModuleCat.{max u (v + 1) uL} R,
      Injective N → ∀ q : ℕ, IsZero ((etaleCompactCohomology L h R (q + 1)).obj
        ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N)))
    (M : Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
      ModuleCat.{max u (v + 1) uL} R) (q : ℕ) :
    IsZero ((etaleCompactCohomology L h R (q + 1)).obj
      ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj M)) := by
  let := pointTopology L X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exact isZero_compactDerived_coefficientRestrictedSmoothPointProduct_of_injective
    ρ (etaleTopology X) (distinguishedLiftSystem ρ) (etaleGodementPoints L h) R
      (etalePoints L h) (etaleSelf X) hΓ M q

end Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The exact Godement target follows from compact acyclicity for injective independent
coefficient diagrams. This analytic input remains a premise. -/
theorem analyticEtaleGodementCompactAcyclic_of_injectiveCoefficients
    (hΓ : T2Space (localizedSpaceFunctor.obj X) →
      Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
        ∀ N : Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
          ModuleCat.{max u (v + 1) uL} R,
          Injective N → ∀ q : ℕ, IsZero ((etaleCompactCohomology L h R (q + 1)).obj
            ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N))) :
    AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ := by
  intro hT2 hX hcontinuous F q
  exact (isZero_etaleCompactCohomology_coefficientRestrictedSmoothPointProduct_of_injective
    L ρ h R (hΓ hT2 hX hcontinuous) ((etaleGodementCoefficientFunctor L ρ h R).obj F) q).of_iso
      ((etaleCompactCohomology L h R (q + 1)).mapIso
        ((etaleRestrictedGodementPointProductIso L ρ h R).app F))

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
