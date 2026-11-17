import Langlands.Sheaf.Equivariant.AnalyticSmoothPointProductOrdinaryAcyclic
import Langlands.Sheaf.Equivariant.TwistedPointProductExact

/-! # The actual discrete coefficients in the ordinary compact-acyclicity reduction -/

noncomputable section

universe u v uL z

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Discrete coefficient diagrams give the same actual restricted smooth product
as the independent-family construction used in the cutoff and c-softness proofs. -/
def etaleCoefficientSmoothPointProductIso
    (N : Discrete
      (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
        ModuleCat.{max u (v + 1) uL} R) :
    (haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R;
      (TwistedOver.coefficientRestrictedSmoothPointProductFunctor ρ (etaleTopology X)
        (distinguishedLiftSystem ρ) (etaleGodementPoints.{u, v, uL} L h) R).obj N) ≅
      etaleRestrictedSmoothPointProduct L h ρ
        ((piEquivalenceFunctorDiscrete _ (ModuleCat.{max u (v + 1) uL} R)).inverse.obj N) :=
  Iso.refl _

/-- The general c-soft theorem gives the exact ordinary compact-vanishing
conclusion for the actual discrete coefficient functor, without requiring
injectivity of the coefficient diagram. -/
theorem isZero_ordinaryCompactCohomology_coefficientSmoothPointProduct_of_cSoftAcyclicity
    (hA : CSoftAcyclicityStatement.{max u (v + 1) uL})
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ)
    (N : Discrete
      (ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) ⥤
        ModuleCat.{max u (v + 1) uL} R) (q : ℕ) :
    IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).obj
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
        (haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R;
          (TwistedOver.coefficientRestrictedSmoothPointProductFunctor ρ (etaleTopology X)
            (distinguishedLiftSystem ρ) (etaleGodementPoints.{u, v, uL} L h) R).obj N))) := by
  have hz := isZero_ordinaryCompactCohomology_smoothPointProduct_of_cSoftAcyclicity L h ρ
    ((piEquivalenceFunctorDiscrete _ (ModuleCat.{max u (v + 1) uL} R)).inverse.obj N) hA hρ q
  exact hz.of_iso
    ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).mapIso
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).mapIso
        (etaleCoefficientSmoothPointProductIso L h ρ R N)))

end Langlands.Sheaf.Equivariant.Analytic
