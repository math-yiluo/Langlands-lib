import Langlands.BruhatTits.IntegralModels.IntegralTorusHomExtension
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusClause
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom

/-! # Actual torus homomorphisms in recovered apartment models -/

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

/-- Extend the specified map between the actual generic tori. -/
def homToSplitTorus : A.torus ⟶ B.torus :=
  B.fieldHomExtension hA
    ((CommGroupScheme.isoOfGroupIso
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus)
      (U := S) A.genericIso).hom ≫ f)

/-- The extension retains both supplied generic identifications. -/
theorem homToSplitTorus_generic_comm :
    (GroupScheme.baseChange (Spec.algebraMap R K)).map
        (CommGroupScheme.groupHom (A.homToSplitTorus hA B f)) ≫
      CommGroupScheme.groupHom B.genericIso.hom =
        A.genericIso.hom ≫ CommGroupScheme.groupHom f := by
  exact congrArg CommGroupScheme.groupHom
    (B.fieldHomExtension_generic_comm hA
      ((CommGroupScheme.isoOfGroupIso
        (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus)
        (U := S) A.genericIso).hom ≫ f))

/-- Generic factorization gives literal compatibility with the original
integral ambient inclusions. -/
theorem homToSplitTorus_comp_inclusion
    (hf : CommGroupScheme.groupHom f ≫ i' = i) :
    CommGroupScheme.groupHom (A.homToSplitTorus hA B f) ≫ B.inclusion =
      A.inclusion := by
  apply B.fieldHomExtension_comp_inclusion
  rw [A.generic_comm]
  change A.genericIso.hom ≫ i =
    (A.genericIso.hom ≫ CommGroupScheme.groupHom f) ≫ i'
  rw [Category.assoc, hf]

end IntegralTorusData

namespace UnramifiedComponentModelRecovery

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {D : RelativeComponentModelData ↥𝒪[F] F G}
  {E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  (e : UnramifiedComponentModelRecovery D E)
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (A : IntegralTorusData D S i) (hA : IsSplitTorus A.torus.toGrp)

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- Pull back the actual lower torus and its inclusion, then use the supplied
neutral-model recovery isomorphism. -/
def baseChangeTorus : IntegralTorusData E
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i) where
  torus := (CommGroupScheme.baseChange
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).obj A.torus
  genericIso := (A.splitTorusModel hA).baseChangeUnramified.genericIso
  inclusion := (GroupScheme.baseChange
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map A.inclusion ≫
      e.neutralIso.iso.hom
  generic_comm := by
    rw [Functor.map_comp, Category.assoc, e.neutralIso.generic_comm]
    simp only [Iso.refl_hom, Category.comp_id]
    exact ((A.splitTorusModelInclusion hA).baseChangeCoefficients
      (fixedFieldIntegers F) (inertiaFixedField F)).generic_comm

theorem baseChangeTorus_isSplit :
    IsSplitTorus (e.baseChangeTorus A hA).torus.toGrp :=
  hA.baseChange (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))

@[simp] theorem baseChangeTorus_inclusion :
    (e.baseChangeTorus A hA).inclusion =
      (GroupScheme.baseChange
        (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map A.inclusion ≫
          e.neutralIso.iso.hom := rfl

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

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The base change of the prescribed lower torus, included in the actual
upper neutral model using recovery. -/
def baseChangedLowerApartmentTorus : IntegralTorusData M.upper
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) :=
  M.recovery.baseChangeTorus (M.lowerApartmentTorus C hDC hiS hf)
    (M.lowerApartmentTorus_isClosedSplit C hDC hiS hf).1

theorem baseChangedLowerApartmentTorus_isSplit :
    IsSplitTorus (M.baseChangedLowerApartmentTorus C hDC hiS hf).torus.toGrp :=
  M.recovery.baseChangeTorus_isSplit (M.lowerApartmentTorus C hDC hiS hf)
    (M.lowerApartmentTorus_isClosedSplit C hDC hiS hf).1

variable (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

/-- An actual integral map from the base-changed prescribed lower torus to
the prescribed upper torus, extending the supplied generic factor map. -/
def apartmentTorusMap :
    (M.baseChangedLowerApartmentTorus C hDC hiS hf).torus ⟶
      (M.upperNeutralApartmentTorus hG hiT C hDC).torus :=
  (M.baseChangedLowerApartmentTorus C hDC hiS hf).homToSplitTorus
    (M.baseChangedLowerApartmentTorus_isSplit C hDC hiS hf)
    (M.upperNeutralApartmentTorus hG hiT C hDC)
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)

/-- The map commutes literally with the recovered neutral inclusions. -/
theorem apartmentTorusMap_comp_inclusion :
    CommGroupScheme.groupHom (M.apartmentTorusMap C hDC hiS hf hG hiT) ≫
        (M.upperNeutralApartmentTorus hG hiT C hDC).inclusion =
      (GroupScheme.baseChange
        (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))).map
          (M.lowerApartmentTorus C hDC hiS hf).inclusion ≫
        M.recovery.neutralIso.iso.hom := by
  apply IntegralTorusData.homToSplitTorus_comp_inclusion
  change (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map
      (CommGroupScheme.groupHom f) ≫
    (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
    (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS
  rw [← Functor.map_comp, hf]

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
