import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusMap
import Langlands.BruhatTits.IntegralModels.IntegralTorusCharacterNaturality
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent

/-! # The specified generic map of recovered apartment tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S S' : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {i' : S'.toGrp ⟶ G}
  (A : IntegralTorusData D S i) (hA : IsSplitTorus A.torus.toGrp)
  (B : IntegralSplitTorusData D.neutral i') (f : S ⟶ S')

/-- Expressed in the prescribed generic coordinates, the integral extension
is exactly the supplied generic torus morphism. -/
@[simp] theorem genericFibreMap_homToSplitTorus :
    A.genericFibreMap B.toIntegralTorusData (A.homToSplitTorus hA B f) = f := by
  change (CommGroupScheme.isoOfGroupIso A.genericIso).inv ≫
      ((CommGroupScheme.baseChange (Spec.algebraMap R K)).map
        (B.fieldHomExtension hA
          ((CommGroupScheme.isoOfGroupIso A.genericIso).hom ≫ f)) ≫
        B.genericIso.hom) = f
  rw [B.fieldHomExtension_generic_comm]
  simp only [Iso.inv_hom_id_assoc]

end IntegralTorusData

namespace RecoveredApartmentFixerModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  {Ω : Set D.Apartment}
  (M : RecoveredApartmentFixerModels D Ω)
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {f : S ⟶ T}
  (hiS : IsMaximalSplitTorus iS)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)

local instance recoveredGenericIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance recoveredGenericIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

variable (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

/-- The actual generic-fibre map of the recovered integral apartment torus
map, expressed on the prescribed generic tori. -/
def apartmentTorusGenericMap :
    (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S ⟶
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T :=
  (M.baseChangedLowerApartmentTorus C hDC hiS hf).genericFibreMap
    (M.upperNeutralApartmentTorus hG hiT C hDC).toIntegralTorusData
    (M.apartmentTorusMap C hDC hiS hf hG hiT)

/-- The recovered apartment torus map induces the coefficient pullback of
its specified generic factor map on the supplied generic tori. -/
@[simp] theorem genericFibreMap_apartmentTorusMap :
    (M.baseChangedLowerApartmentTorus C hDC hiS hf).genericFibreMap
        (M.upperNeutralApartmentTorus hG hiT C hDC).toIntegralTorusData
        (M.apartmentTorusMap C hDC hiS hf hG hiT) =
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f := by
  exact IntegralTorusData.genericFibreMap_homToSplitTorus _ _ _ _

/-- The actual generic-fibre map recovers the coefficient pullback of the
prescribed lower-to-upper torus map. -/
@[simp] theorem apartmentTorusGenericMap_eq :
    M.apartmentTorusGenericMap C hDC hiS hf hG hiT =
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f := by
  exact M.genericFibreMap_apartmentTorusMap C hDC hiS hf hG hiT

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
