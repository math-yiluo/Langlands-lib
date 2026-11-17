import Langlands.Cohomology.AnalyticEtaleGodementCoefficientReduction
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleCohomology

/-! # The local higher-direct-image obligation for actual smooth point products -/

noncomputable section

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

/-- Positive ordinary higher direct images of the actual restricted smooth point
product vanish on injective independent coefficient diagrams. This local analytic
input is unproved. -/
def AnalyticEtaleSmoothPointProductLocalAcyclicStatement : Prop :=
  T2Space (localizedSpaceFunctor.obj X) →
    Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
      ∀ N : Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
        ModuleCat.{max u (v + 1) uL} R,
        Injective N → ∀ q : ℕ,
          IsZero ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj
            ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N))

/-- The local higher-direct-image input and ordinary compact acyclicity together
supply the exact analytic Godement compact-acyclicity target. Both inputs remain
explicit hypotheses. -/
theorem analyticEtaleGodementCompactAcyclic_of_local_and_ordinary
    (hlocal : AnalyticEtaleSmoothPointProductLocalAcyclicStatement L X h R G ρ)
    (hordinary : T2Space (localizedSpaceFunctor.obj X) →
      Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
        ∀ N : Discrete (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
          ModuleCat.{max u (v + 1) uL} R,
          Injective N → ∀ q : ℕ,
            IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).obj
              ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
                ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N)))) :
    AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ := by
  apply analyticEtaleGodementCompactAcyclic_of_injectiveCoefficients L X h R G ρ
  intro hT2 hX hcontinuous N hN q
  let := hT2
  exact isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic
    R L h hX ((etaleCoefficientRestrictedSmoothPointProductFunctor L ρ h R).obj N)
      (hlocal hT2 hX hcontinuous N hN) q (hordinary hT2 hX hcontinuous N hN q)

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
