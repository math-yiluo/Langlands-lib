import Langlands.Cohomology.DivisibleSystem.AnalyticEtale
import Langlands.Geometry.Analytic.CommonPointField.Proof
import Langlands.Geometry.Analytic.EtaleGeometricPointProof
import Langlands.Geometry.Analytic.QuasiEtaleFieldPointImageLift
import Langlands.Sheaf.Equivariant.AnalyticEtaleGodement
import Langlands.Sheaf.Equivariant.AnalyticEtalePointDetection
import Langlands.Sheaf.Equivariant.TwistedSmoothGodementExactness

/-! # Godement resolution systems from geometric points of the analytic étale site -/

noncomputable section

universe u v uL z

namespace Langlands.Cohomology.DivisibleSystem.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic Langlands.Sheaf.Equivariant.TwistedOver

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

section Points

variable (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [IsAlgClosed L] [NormedAlgebra K L]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- When `L` realizes all points of the base, its actual étale site fibers jointly detect
module-sheaf morphisms. An `L`-point over an arbitrary point of a site object is obtained
by the pointed lift for its étale structure map. -/
theorem etaleGeometricGodementPoints_jointlyFaithful
    (hL : Function.Surjective (pointProjection L X)) :
    JointlyFaithful fun x =>
      (etaleGodementPoints L (EtaleSite.geometricPointStatement K L X) x).sheafFiber
        (A := ModuleCat.{max u (v + 1) uL} R) := by
  have h := etalePointFibers_jointlyFaithful_of_objectwise_surjective
    (R := R) L (EtaleSite.geometricPointStatement K L X) (by
      intro U y
      obtain ⟨x, hx⟩ := hL (localizedSpaceFunctor.map U.hom y)
      obtain ⟨p, hp, _⟩ := pointedFieldPointLift_of_etale (L := L) U.prop x y hx.symm
      exact ⟨p, hp⟩)
  exact ⟨fun hfg => h.map_injective (fun x => hfg ⟨x⟩)⟩

end Points

/-- A small geometric point family with jointly faithful étale module fibers exists
on the actual analytic space. -/
theorem exists_etaleGeometricGodementPointFamily (X : LocalizedCategory.{u, v, v} (K := K))
    (R : Type (max u (v + 1) uL)) [CommRing R] :
    ∃ (I : Type (max u (v + 1) uL))
      (points : I → (etaleTopology X).Point.{max u (v + 1) uL}),
      JointlyFaithful fun x => (points x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R) := by
  obtain ⟨L, nL, uL', cL, aL, kL, hL⟩ := commonAlgebraicallyClosedPointField.{u, v, uL} K X
  refine ⟨_, etaleGodementPoints L (EtaleSite.geometricPointStatement K L X), ?_⟩
  exact etaleGeometricGodementPoints_jointlyFaithful L R (fun y => by
    obtain ⟨x, hx⟩ := hL (ULift.up y)
    exact ⟨x, congrArg ULift.down hx⟩)

section Resolution

variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
  (R : Type (max u (v + 1) uL)) [CommRing R] [Small.{max u (v + 1) uL} G]
  [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable {ℓ : ℕ} (T : EtaleDivisibleSystem.{u, v, uL} ρ R ℓ)

/-- Choose the family from the common point field and retain its joint faithfulness. -/
def etaleGeometricGodementPointFamily :
    Σ I : Type (max u (v + 1) uL),
      {points : I → (etaleTopology X).Point.{max u (v + 1) uL} //
        JointlyFaithful fun x => (points x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R)} :=
  let h := exists_etaleGeometricGodementPointFamily.{u, v, uL} X R
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

/-- The termwise Godement resolution of an actual `ℓ`-divisible system of analytic
étale `G`-sheaves. Exactness and joint faithfulness are supplied by the geometric
point family and the exact locally discrete Godement functor. -/
def etaleGeometricGodementResolutionSystem : EtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  let family := etaleGeometricGodementPointFamily.{u, v, uL} (X := X) R
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI : PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ family.2.1 R) :=
    smoothGodementZero_preservesFiniteLimits ρ (etaleTopology X) (distinguishedLiftSystem ρ)
      family.2.1 R
  haveI : PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ family.2.1 R) :=
    smoothGodementZero_preservesFiniteColimits ρ (etaleTopology X) (distinguishedLiftSystem ρ)
      family.2.1 R
  etaleFamilyGodementResolutionSystem.{u, v, uL} ρ family.2.1 R T family.2.2

/-- Each level of the geometric Godement resolution is exact in positive degrees. -/
theorem etaleGeometricGodementResolutionSystem_exactAt (m q : ℕ) :
    have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    ((etaleGeometricGodementResolutionSystem.{u, v, uL} ρ R T).obj m).ExactAt (q + 1) := by
  let family := etaleGeometricGodementPointFamily.{u, v, uL} (X := X) R
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have : PreservesFiniteLimits (etaleFamilyGodementFunctor.{u, v, uL} ρ family.2.1 R) :=
    smoothGodementZero_preservesFiniteLimits ρ (etaleTopology X) (distinguishedLiftSystem ρ)
      family.2.1 R
  have : PreservesFiniteColimits (etaleFamilyGodementFunctor.{u, v, uL} ρ family.2.1 R) :=
    smoothGodementZero_preservesFiniteColimits ρ (etaleTopology X) (distinguishedLiftSystem ρ)
      family.2.1 R
  exact etaleFamilyGodementResolutionSystem_obj_exactAt.{u, v, uL} ρ family.2.1 R T family.2.2 m q

end Resolution

end Langlands.Cohomology.DivisibleSystem.Analytic
