import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRoots
import Langlands.BruhatTits.IntegralModels.IntegralTorus

/-! # The lower integral split torus from recovered full fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {iT : T.toGrp ⟶ G} {f : S ⟶ T}

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

private instance recoveredTorusExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

private def commIsoToGroupIso {B : Scheme.{u}} {A A' : CommGroupScheme B}
    (e : A ≅ A') : A.toGrp ≅ A'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id

/-- Scalar units of the original torus, over the unramified field, belong to
the full one-fixer of every subset of the upper apartment. -/
theorem map_lowerTorus_characterValuationKernel_le_oneFixer
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (Ω : Set D.Apartment) :
    (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) S.toGrp)).map
        (rationalPoints.map
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)) ≤
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω) := by
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨IntegerValuation.map_mem_characterValuationKernel
    (MaximalUnramified.valuation F) _ hs, D.mem_pointwiseFixer.mpr ?_⟩
  rintro _ ⟨x, -, rfl⟩
  have hfix := D.map_torusUnits_smul_apartmentMap
    (MaximalUnramified.valuation F) C hDC
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
    s hs x
  have hfK :
      CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  rwa [hfK] at hfix

/-- Recovery of a full fixer model constructs the lower closed split torus
inside the neutral model. No equality for neutral integral points is required. -/
theorem exists_closedSplitIntegralTorus_of_fullRecovery
    (hiS : IsMaximalSplitTorus iS)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (L : RelativeComponentModelData ↥𝒪[F] F G)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (e : UnramifiedComponentModelRecovery L E) (Ω : Set D.Apartment)
    (hE : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω)) :
    ∃ A : IntegralTorusData L S iS, A.IsClosedSplit := by
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have hb : (characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) S.toGrp)).map
        (rationalPoints.map
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)) ≤
      L.full.baseChangeUnramified.integralPoints := by
    rw [e.full_integralPoints_eq, hE]
    exact map_lowerTorus_characterValuationKernel_le_oneFixer D C hf hDC Ω
  have hv (a : (fixedFieldIntegers F)ˣ) :
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 :=
    (MaximalUnramified.valuation_isEquiv F).eq_one_iff_eq_one.mpr
      ((Langlands.LocalGalois.Separable.isUnit_iff_eq_one (fixedFieldValuation F)
        (a : fixedFieldIntegers F)).mp a.isUnit)
  obtain ⟨𝒮, j, eS, h𝒮, hj, hgen⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_baseChange
      L.full (fixedFieldIntegers F) (inertiaFixedField F)
      (MaximalUnramified.valuation F) hv
      (fun x hx => (IntegralModel.unramifiedIntegerRange_intersection x).mp hx)
      iS hiS.isSplitSubtorus.1 hiS.isSplitSubtorus.2 hb
  let A : IntegralSplitTorusData L.full iS :=
    { torus := 𝒮
      isSplit := h𝒮
      inclusion := j
      genericIso := eS
      generic_comm := hgen }
  let B := A.factorNeutral L
  refine ⟨
    { torus := B.torus
      genericIso := commIsoToGroupIso B.genericIso
      inclusion := B.inclusion
      generic_comm := B.generic_comm },
    B.isSplit, ?_⟩
  exact A.factorNeutral_isClosedSubgroup L hj

/-- A chosen actual lower closed split torus in the recovered neutral model. -/
def integralTorusOfFullRecovery
    (hiS : IsMaximalSplitTorus iS)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (L : RelativeComponentModelData ↥𝒪[F] F G)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (e : UnramifiedComponentModelRecovery L E) (Ω : Set D.Apartment)
    (hE : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω)) :
    IntegralTorusData L S iS :=
  Classical.choose (exists_closedSplitIntegralTorus_of_fullRecovery D C
    hiS hf hDC L E e Ω hE)

theorem integralTorusOfFullRecovery_isClosedSplit
    (hiS : IsMaximalSplitTorus iS)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (L : RelativeComponentModelData ↥𝒪[F] F G)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (e : UnramifiedComponentModelRecovery L E) (Ω : Set D.Apartment)
    (hE : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω)) :
    (integralTorusOfFullRecovery D C hiS hf hDC L E e Ω hE).IsClosedSplit :=
  Classical.choose_spec (exists_closedSplitIntegralTorus_of_fullRecovery D C
    hiS hf hDC L E e Ω hE)

end Langlands.BruhatTits.IntegralModels
