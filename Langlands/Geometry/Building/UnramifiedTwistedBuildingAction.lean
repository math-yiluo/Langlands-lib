import Langlands.Geometry.Building.SemilinearCocycleAction
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof

/-! # Cocycle twists on the actual maximal-unramified building -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance extendedAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

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

/-- The twist acts on the original reduced-building quotient. -/
def twistedAction : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
    Equiv.Perm B.ReducedBuilding :=
  SemilinearCocycleAction.action (rationalConjugateAction F (inertiaFixedField F) G)
    A.action A.action_smul c hc

@[simp] theorem twistedAction_apply
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (y : B.ReducedBuilding) :
    A.twistedAction c hc σ y = c σ • A.action σ y := rfl

/-- A coefficient-fixed point has finite twisted orbit for a finite-level cocycle. -/
theorem finite_twisted_orbit_of_fixed (y : B.ReducedBuilding)
    (hy : ∀ σ, A.action σ y = y)
    (hfin : ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) :
    (Set.range fun σ => A.twistedAction c hc σ y).Finite := by
  obtain ⟨E, hE, hfix⟩ := hfin
  have : FiniteDimensional F E := hE
  have hfinite : (Set.range c).Finite :=
    SemilinearCocycleAction.finite_range_of_finite_fixing_field F (inertiaFixedField F)
      (rationalConjugateAction F (inertiaFixedField F) G) c hc E hfix
  exact SemilinearCocycleAction.finite_orbit_of_fixed
    (rationalConjugateAction F (inertiaFixedField F) G) A.action A.action_smul c hc y hy hfinite

end MaximalUnramified.SemilinearApartmentData

namespace UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
  (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))
  (hc : ∀ σ τ, c (σ * τ) =
    c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))

set_option maxHeartbeats 1600000 in
include hc in
/-- The exact building and coefficient action used by the twisted-chamber target
have a finite twisted orbit. -/
theorem exists_finite_twisted_orbit (hG : IsConnectedReductive G)
    (hfin : ∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
      ∀ σ ∈ E.fixingSubgroup, c σ = 1) :
    ∃ y : (buildingData iT hGK hiT D C h6).ReducedBuilding,
      (Set.range fun σ => c σ • (semilinearData iT hGK hiT C h6 hD).action σ y).Finite := by
  obtain ⟨x, hx⟩ := unramifiedGaloisFixedApartment F G hG T iT hiT D hD
  have hx' : ∀ σ, KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x = x :=
    fun σ => KPApartmentData.Apartment.ext (hx σ)
  refine ⟨D.apartmentMap x, ?_⟩
  have hy : ∀ σ, (semilinearData iT hGK hiT C h6 hD).action σ (D.apartmentMap x) =
      D.apartmentMap x := by
    intro σ
    rw [MaximalUnramified.SemilinearApartmentData.action_apartmentMap]
    exact congrArg D.apartmentMap (hx' σ)
  exact (semilinearData iT hGK hiT C h6 hD).finite_twisted_orbit_of_fixed c hc
    (D.apartmentMap x) hy hfin

end UnramifiedBuildingDescent

end Langlands.Geometry.Building
