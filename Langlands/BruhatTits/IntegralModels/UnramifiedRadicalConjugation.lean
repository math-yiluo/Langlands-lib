import Langlands.GroupScheme.IntegralModel.SpecialFibreSubgroupPoints
import Langlands.BruhatTits.IntegralModels.Transport.Model
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Conjugating special-fibre preimages into an unramified apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

section Transport

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) (f : G ≅ H)

/-- Transport changes the generic image of a special-fibre preimage by the
same rational-point isomorphism. -/
theorem transport_specialFibreSubgroupPoints
    (P : Subgroup (rationalPoints M.specialFibre)) :
    (M.transport f).specialFibreSubgroupPoints P =
      (M.specialFibreSubgroupPoints P).map (rationalPoints.map f.hom) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨M.integralPointMap x, ⟨x, hx, rfl⟩,
      (M.transport_integralPointMap f x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, M.transport_integralPointMap f x⟩

/-- A computation after transport by `Int(g⁻¹)` recovers the original
special-fibre preimage by conjugating by `g`. -/
theorem specialFibreSubgroupPoints_eq_map_innerIso
    (P : Subgroup (rationalPoints M.specialFibre)) (g : rationalPoints G) :
    M.specialFibreSubgroupPoints P =
      ((M.transport (G.innerIso g⁻¹)).specialFibreSubgroupPoints P).map
        (MulAut.conj g).toMonoidHom := by
  rw [M.transport_specialFibreSubgroupPoints, rationalPoints_map_innerIso,
    Subgroup.map_map]
  have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (rationalPoints G) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc, Subgroup.map_id]

end Transport

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]

set_option maxHeartbeats 1600000 in
/-- Transport by `Int(g⁻¹)` removes a translate from the characterized
integral points while keeping the same zero datum. -/
theorem integralPoints_transport_innerIso_same_zeroDatum
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (g : rationalPoints G) (Y : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hM : M.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)) :
    (M.transport (G.innerIso g⁻¹)).integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Y) := by
  have hzero : E.zeroPoints.map (rationalPoints.map (G.innerIso g⁻¹).hom) =
      E.zeroPoints := by
    rw [rationalPoints_map_innerIso]
    exact Subgroup.normal_iff_map_conj_eq.mp E.normal_zeroPoints _
  have hset : (fun x => g • C.apartmentMap x) '' Y =
      (fun y => g • y) '' (C.apartmentMap '' Y) :=
    (Set.image_image _ _ _).symm
  have hfix : (C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)).map
      (rationalPoints.map (G.innerIso g⁻¹).hom) =
        C.pointwiseFixer (C.apartmentMap '' Y) := by
    rw [hset, rationalPoints_map_innerIso]
    change (fixingSubgroup (rationalPoints G)
        ((fun y => g • y) '' (C.apartmentMap '' Y))).map
          (MulAut.conj g⁻¹).toMonoidHom =
      fixingSubgroup (rationalPoints G) (C.apartmentMap '' Y)
    apply SubMulAction.fixingSubgroup_map_conj_eq
    rw [Set.image_smul, inv_smul_smul]
  rw [M.transport_integralPoints, hM,
    Subgroup.map_inf_eq _ _ _ (rationalPoints_map_injective_of_iso _), hzero, hfix]

end Unramified
end Langlands.GroupScheme.IntegralModel
