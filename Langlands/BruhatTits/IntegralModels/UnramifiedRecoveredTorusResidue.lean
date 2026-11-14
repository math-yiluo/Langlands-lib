import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusMap
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelBaseChange

/-! # Residue comparison squares for the recovered apartment tori -/

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

namespace UnramifiedComponentModelRecovery

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {D : RelativeComponentModelData ↥𝒪[F] F G}
  {E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  (e : UnramifiedComponentModelRecovery D E)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The actual residue coefficient pullback of the lower neutral model,
identified with the upper neutral special fibre by recovery. -/
def neutralResidueBaseChangeIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField ↥𝒪[F])
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj
      D.neutral.specialFibre ≅ E.neutral.specialFibre :=
  D.neutral.specialFibreBaseChangeIso (fixedFieldIntegers F) (inertiaFixedField F) ≪≫
    (GroupScheme.baseChange
      (IntegralModel.residueBaseMap (fixedFieldIntegers F))).mapIso e.neutralIso.iso

variable {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (A : IntegralTorusData D S i) (hA : IsSplitTorus A.torus.toGrp)

/-- Both residue fibres of the actual pulled-back torus are identified by the
canonical coefficient comparison. -/
def baseChangeTorusSpecialFibreIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField ↥𝒪[F])
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj
      A.specialFibre.toGrp ≅ (e.baseChangeTorus A hA).specialFibre.toGrp :=
  (A.splitTorusModel hA).specialFibreBaseChangeIso
    (fixedFieldIntegers F) (inertiaFixedField F)

/-- The actual residue inclusions commute with coefficient comparison and
the supplied neutral-model recovery. -/
theorem baseChangeTorusSpecialFibreIso_comp_inclusion :
    (e.baseChangeTorusSpecialFibreIso A hA).hom ≫
        (e.baseChangeTorus A hA).specialFibreInclusion =
      (GroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField ↥𝒪[F])
          (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
        A.specialFibreInclusion ≫ e.neutralResidueBaseChangeIso.hom := by
  have h := congrArg
    (fun g => g ≫ (GroupScheme.baseChange
      (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map e.neutralIso.iso.hom)
    ((A.splitTorusModelInclusion hA).specialFibreBaseChangeIso_naturality
      (fixedFieldIntegers F) (inertiaFixedField F)).symm
  simpa only [baseChangeTorusSpecialFibreIso, IntegralTorusData.specialFibreInclusion,
    baseChangeTorus, neutralResidueBaseChangeIso, IntegralModel.Hom.specialFibreMap,
    IntegralModel.Hom.baseChangeCoefficients, IntegralTorusData.splitTorusModelInclusion,
    Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using h

end UnramifiedComponentModelRecovery

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
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The actual residue coefficient comparison for the prescribed lower
apartment torus. -/
def apartmentTorusSpecialFibreIso :
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField ↥𝒪[F])
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj
      (M.lowerApartmentTorus C hDC hiS hf).specialFibre.toGrp ≅
        (M.baseChangedLowerApartmentTorus C hDC hiS hf).specialFibre.toGrp :=
  M.recovery.baseChangeTorusSpecialFibreIso
    (M.lowerApartmentTorus C hDC hiS hf)
    (M.lowerApartmentTorus_isClosedSplit C hDC hiS hf).1

/-- Specializing the actual apartment torus map gives the original lower
residue inclusion followed by actual neutral-model recovery. -/
theorem apartmentTorusMap_specialFibre_comp_inclusion :
    (M.apartmentTorusSpecialFibreIso C hDC hiS hf).hom ≫
      (GroupScheme.baseChange
        (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        (CommGroupScheme.groupHom (M.apartmentTorusMap C hDC hiS hf hG hiT)) ≫
      (M.upperNeutralApartmentTorus hG hiT C hDC).specialFibreInclusion =
    (GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField ↥𝒪[F])
        (IsLocalRing.ResidueField (fixedFieldIntegers F)))).map
      (M.lowerApartmentTorus C hDC hiS hf).specialFibreInclusion ≫
        M.recovery.neutralResidueBaseChangeIso.hom := by
  change (M.apartmentTorusSpecialFibreIso C hDC hiS hf).hom ≫
      (GroupScheme.baseChange
        (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        (CommGroupScheme.groupHom (M.apartmentTorusMap C hDC hiS hf hG hiT)) ≫
      (GroupScheme.baseChange
        (IntegralModel.residueBaseMap (fixedFieldIntegers F))).map
        (M.upperNeutralApartmentTorus hG hiT C hDC).inclusion = _
  rw [← Functor.map_comp, M.apartmentTorusMap_comp_inclusion]
  exact M.recovery.baseChangeTorusSpecialFibreIso_comp_inclusion
    (M.lowerApartmentTorus C hDC hiS hf)
    (M.lowerApartmentTorus_isClosedSplit C hDC hiS hf).1

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
