import Langlands.Sheaf.Equivariant.AnalyticSmoothPointProductCSoft
import Langlands.Sheaf.Equivariant.AnalyticOrdinaryUniverseDerived
import Langlands.Cohomology.CompactSoft.Statement

/-! # Ordinary compact acyclicity reduced to the general c-soft theorem -/

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
variable {R : Type (max u (v + 1) uL)} [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable (M : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
  ModuleCat.{max u (v + 1) uL} R)

/-- The actual ordinary compact cohomology of the smooth point product equals
native compact cohomology of its canonically lifted ordinary sheaf. -/
def etaleRestrictedSmoothPointProductOrdinaryCohomologyIso (q : ℕ) :
    (underlyingTopologyCompactCohomology.{u, v, uL} X R q).obj
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
          (etaleRestrictedSmoothPointProduct L h ρ M)) ≅
      (TopologicalDerivedSections.compactCohomology
        (TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) R q).obj
          (Langlands.Sheaf.CompactExtension.universeLift.{v, max u (v + 1) uL}
            ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
              (etaleRestrictedSmoothPointProduct L h ρ M))) :=
  (underlyingTopologyLiftCompactCohomologyIso.{u, v, uL} X R q).app _

/-- The ordinary compact-acyclicity input is fully reduced to the existing
general c-soft acyclicity statement. That general theorem remains explicit. -/
theorem isZero_ordinaryCompactCohomology_smoothPointProduct_of_cSoftAcyclicity
    (hA : CSoftAcyclicityStatement.{max u (v + 1) uL})
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ) (q : ℕ) :
    IsZero ((underlyingTopologyCompactCohomology.{u, v, uL} X R (q + 1)).obj
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
        (etaleRestrictedSmoothPointProduct L h ρ M))) := by
  have := locallyCompactSpace_localized X
  have : LocallyCompactSpace
      (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X)) :=
    (Homeomorph.ulift.{max u (v + 1) uL, v}
      (X := localizedSpaceFunctor.obj X)).locallyCompactSpace_iff.2 inferInstance
  have hz := hA
    (TopCat.of (ULift.{max u (v + 1) uL} (localizedSpaceFunctor.obj X))) R
      (Langlands.Sheaf.CompactExtension.universeLift.{v, max u (v + 1) uL}
        ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
          (etaleRestrictedSmoothPointProduct L h ρ M)))
      (isCSoft_universeLift_etaleRestrictedSmoothPointProduct L h ρ M hρ) q
  exact hz.of_iso
    (etaleRestrictedSmoothPointProductOrdinaryCohomologyIso L h ρ M (q + 1))

/-- The remaining local higher-direct-image input, together with the general
c-soft theorem, implies actual étale compact acyclicity of this smooth product. -/
theorem isZero_etaleCompactCohomology_smoothPointProduct_of_local_and_cSoft
    (hA : CSoftAcyclicityStatement.{max u (v + 1) uL})
    [T2Space (localizedSpaceFunctor.obj X)]
    (hX : Function.Surjective (pointProjection L X)) (hρ : IsContinuousAction ρ)
    (hlocal : ∀ q : ℕ, IsZero
      ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj
        (etaleRestrictedSmoothPointProduct L h ρ M))) (q : ℕ) :
    IsZero ((etaleCompactCohomology L h R (q + 1)).obj
      (etaleRestrictedSmoothPointProduct L h ρ M)) :=
  isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic
    R L h hX (etaleRestrictedSmoothPointProduct L h ρ M) hlocal q
      (isZero_ordinaryCompactCohomology_smoothPointProduct_of_cSoftAcyclicity L h ρ M hA hρ q)

end Langlands.Sheaf.Equivariant.Analytic
