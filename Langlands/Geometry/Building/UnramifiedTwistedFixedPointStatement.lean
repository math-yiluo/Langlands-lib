import Langlands.Geometry.Building.UnramifiedBuildingMetricStatement
import Langlands.Geometry.Building.UnramifiedTwistedBuildingAction
import Langlands.Geometry.Metric.KPBoundedActionFixedPointProof

/-! # Twisted fixed points from a complete NPC metric -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedTwistedFixedPointAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Finite-level cocycle twists of the supplied maximal-unramified building
have a common fixed point. This is the fixed-point prerequisite for stable chambers. -/
def UnramifiedTwistedFixedPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    let _ : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
        (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          rationalPoints (baseChanged F (inertiaFixedField F) G)),
        (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
        (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
          ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
        ∃ y : (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).ReducedBuilding,
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            c σ • (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ y = y

namespace MaximalUnramified.SemilinearApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}
  (A : MaximalUnramified.SemilinearApartmentData B)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))

/-- A supplied complete NPC realization and one finite twisted orbit give a
common fixed point for the original twisted permutations. -/
theorem exists_twisted_fixed_point (R : A.MetricRealization)
    (x : B.ReducedBuilding)
    (hx : (Set.range fun σ => A.twistedAction c hc σ x).Finite) :
    ∃ y : B.ReducedBuilding, ∀ σ, c σ • A.action σ y = y := by
  let _ : MetricSpace B.ReducedBuilding := R.metric
  let _ : CompleteSpace B.ReducedBuilding := R.complete
  let _ : IsIsometricSMul
      (rationalPoints (baseChanged F (inertiaFixedField F) G)) B.ReducedBuilding := R.isometric
  let _ : Nonempty B.ReducedBuilding := ⟨x⟩
  let _ : MulAction (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) B.ReducedBuilding :=
    MulAction.compHom B.ReducedBuilding (A.twistedAction c hc)
  let _ : IsIsometricSMul (inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      B.ReducedBuilding := by
    refine ⟨fun σ => ?_⟩
    change Isometry (fun z => c σ • A.action σ z)
    exact (isometry_smul B.ReducedBuilding (c σ)).comp (R.coefficient_isometry σ)
  have hbdd : Langlands.Geometry.Metric.KP.HasBoundedAction B.ReducedBuilding
      (Set.univ : Set (inertiaFixedField F ≃ₐ[F] inertiaFixedField F)) := by
    refine ⟨x, ?_⟩
    rw [Set.image_univ]
    change Bornology.IsBounded (Set.range fun σ => A.twistedAction c hc σ x)
    exact hx.isBounded
  obtain ⟨y, hy⟩ := Langlands.Geometry.Metric.KP.boundedActionFixedPoint
    B.ReducedBuilding R.nonpositivelyCurved
    (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) hbdd
  exact ⟨y, hy⟩

end MaximalUnramified.SemilinearApartmentData

set_option maxHeartbeats 1600000 in
/-- The only additional input needed by the finite-orbit route is the complete
NPC metric realization for the supplied maximal-unramified building. -/
theorem unramifiedTwistedFixedPoint_of_metric :
    UnramifiedBuildingMetricStatement.{u} → UnramifiedTwistedFixedPointStatement.{u} := by
  intro hmetric F _ _ _ _ G hG T iT
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  dsimp only
  intro hiT
  let _ := mono_of_isMaximalSplitTorus hiT
  let _ : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hfin
  let hGK := connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨R⟩ := hmetric F G hG T iT hiT D C h6 hD
  obtain ⟨x, hx⟩ := UnramifiedBuildingDescent.exists_finite_twisted_orbit
    iT hGK hiT D C h6 hD c hc hG hfin
  exact MaximalUnramified.SemilinearApartmentData.exists_twisted_fixed_point
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD) c hc R x hx

end Langlands.Geometry.Building
