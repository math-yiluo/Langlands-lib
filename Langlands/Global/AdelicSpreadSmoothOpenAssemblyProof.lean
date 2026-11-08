import Langlands.Global.AdelicSpreadSmoothOpenAssemblyStatement
import Langlands.Global.CurvePlacePrincipalSIntegerFiniteType
import Langlands.Global.NumberFieldPrincipalSIntegerFiniteType
import Langlands.Global.AdelicSpreadModelMorphisms
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.AlgebraicGeometry.ULiftIntAlgebra

/-! # Assembly of actual adelic openness for smooth geometrically connected maps -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms

/-- A finite-type model over a ring of finite type over the integers is of
finite type over the absolute base in its own universe. -/
lemma locallyOfFiniteType_toSpecULiftZ_of_over (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] (X : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from X.left) := by
  let : Algebra (ULift.{u} ℤ) R := Langlands.ULiftInt.algebra R
  let := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ULift.{u} ℤ) (A := R)
    (Subsingleton.elim _ _)
  have : Algebra.FiniteType (ULift.{u} ℤ) R :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ULift.{u} ℤ) R
  have hft : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have heq : specULiftZIsTerminal.from X.left =
      X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) R)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [heq]
  infer_instance

/-- A morphism of separated quasi-compact models is separated and quasi-compact. -/
lemma over_hom_separated_quasiCompact {B : Scheme.{u}} {M N : Over B}
    [QuasiCompact M.hom] [IsSeparated M.hom] [IsSeparated N.hom] (gm : M ⟶ N) :
    IsSeparated gm.left ∧ QuasiCompact gm.left := by
  have hsep : IsSeparated (gm.left ≫ N.hom) := by
    rw [Over.w gm]
    infer_instance
  have hqc : QuasiCompact (gm.left ≫ N.hom) := by
    rw [Over.w gm]
    infer_instance
  exact ⟨IsSeparated.of_comp gm.left N.hom, QuasiCompact.of_comp gm.left N.hom⟩

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Fixed-model openness at a level whose actual integer ring is of finite
type over the integers. -/
private lemma curve_fixedModel_open
    (hLW : Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u})
    (hsurj : CurvePlaceLevelComponentSurjectivityStatement.{u})
    (hloc : CurvePlaceSmoothLocalPointOpenStatement.{u})
    (hred : CurvePlaceFixedModelAdeleOpenOfLocalStatement.{u})
    (S : Finset (AlgebraicCurve.Place k F)) [Algebra.FiniteType ℤ (curvePlaceSIntegers k F S)]
    (M N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom] [IsSeparated M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] [IsSeparated N.hom]
    (gm : M ⟶ N) [Smooth gm.left] [GeometricallyConnected gm.left] :
    @IsOpenMap _ _ (curvePlaceFixedModelAdelePointTopology k F S M)
      (curvePlaceFixedModelAdelePointTopology k F S N)
      (fun p : CurvePlaceFixedModelAdelePoints k F S M => p ≫ gm) := by
  obtain ⟨hsep, hqc⟩ := over_hom_separated_quasiCompact gm
  refine hred k F S M N gm (fun T i => hloc k F S M N gm T i) ?_
  exact hsurj hLW k F S N M gm
    (locallyOfFiniteType_toSpecULiftZ_of_over (curvePlaceSIntegers k F S) N)
    (QuasiCompact.compactSpace_of_compactSpace N.hom) inferInstance hsep hqc inferInstance

/-- Openness for the spread topologies of compatible models at such a level. -/
private lemma curve_spread_open_of_model
    (hLW : Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u})
    (hsurj : CurvePlaceLevelComponentSurjectivityStatement.{u})
    (hloc : CurvePlaceSmoothLocalPointOpenStatement.{u})
    (hred : CurvePlaceFixedModelAdeleOpenOfLocalStatement.{u})
    (S : Finset (AlgebraicCurve.Place k F)) [Algebra.FiniteType ℤ (curvePlaceSIntegers k F S)]
    (M N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom] [IsSeparated M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] [IsSeparated N.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S M ≅ Y)
    (f : curvePlaceModelGenericFiber k F S N ≅ W)
    (g : Y ⟶ W) (gm : M ⟶ N) [Smooth gm.left] [GeometricallyConnected gm.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map gm ≫
        f.hom = e.hom ≫ g) :
    @IsOpenMap (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S M Y e)
      (curvePlaceSpreadAdelePointTopology k F S N W f)
      (fun p => p ≫ g) := by
  let := curvePlaceFixedModelAdelePointTopology k F S M
  let := curvePlaceFixedModelAdelePointTopology k F S N
  let := curvePlaceSpreadAdelePointTopology k F S M Y e
  let := curvePlaceSpreadAdelePointTopology k F S N W f
  let eM := curvePlaceSpreadAdelePointHomeomorph k F S M Y e
  let eN := curvePlaceSpreadAdelePointHomeomorph k F S N W f
  have hn (p : CurvePlaceFixedModelAdelePoints k F S M) :
      eN (p ≫ gm) = eM p ≫ g := by
    change curvePlaceGenericFiberAdelePointEquiv k F S N (p ≫ gm) ≫ f.hom =
      (curvePlaceGenericFiberAdelePointEquiv k F S M p ≫ e.hom) ≫ g
    rw [curvePlaceGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => curvePlaceGenericFiberAdelePointEquiv k F S M p ≫ q) h
  have hc := eN.isOpenMap.comp
    ((curve_fixedModel_open k F hLW hsurj hloc hred S M N gm).comp eM.symm.isOpenMap)
  have heq : (fun p => p ≫ g) = (eN ∘ (fun p => p ≫ gm) ∘ eM.symm) := by
    funext p
    change p ≫ g = eN (eM.symm p ≫ gm)
    rw [hn, eM.apply_symm_apply]
  exact heq.symm ▸ hc

/-- The generic fibre of a model pulled back to a larger level. -/
private def curveGenericFiberCompIso (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    {U : Finset (AlgebraicCurve.Place k F)} (hSU : S ⊆ U) :
    curvePlaceModelGenericFiber k F U (curvePlaceLevelModelBaseChange k F hSU X) ≅
      curvePlaceModelGenericFiber k F S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) X

end Curve

/-- Function fields: assembly of Conrad's Theorem 4.5 from its inputs. -/
theorem curvePlaceSpreadSmoothOpenAssembly :
    CurvePlaceSpreadSmoothOpenAssemblyStatement.{u} := by
  intro hLW hsurj hloc hred hmodel k F _ _ _ _ _ _ _ S V X Z _ _ _ _ Y W _ _ e f g _ _ _
  let : LocallyOfFiniteType (curvePlaceModelGenericFiber k F S X).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : QuasiCompact (curvePlaceModelGenericFiber k F S X).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType (curvePlaceModelGenericFiber k F V Z).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : QuasiCompact (curvePlaceModelGenericFiber k F V Z).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType Y.hom := by
    rw [← Over.w e.inv]
    infer_instance
  let : QuasiCompact Y.hom := by
    rw [← Over.w e.inv]
    infer_instance
  let : LocallyOfFiniteType W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  let : QuasiCompact W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  obtain ⟨T, M, N, hMft, hMqc, hMsep, hNft, hNqc, hNsep, eT, fT, gm, hgm, hm⟩ :=
    hmodel k F S Y W g ⟨inferInstance, inferInstance⟩
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  let U := curvePlacePrincipalLevelAbove k F T.val
  let : Algebra.FiniteType ℤ (curvePlaceSIntegers k F U.val) :=
    curvePlacePrincipalLevelAbove_finiteType k F T.val
  let a := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F U.property))
  let MU := curvePlaceLevelModelBaseChange k F U.property M
  let NU := curvePlaceLevelModelBaseChange k F U.property N
  let gmU : MU ⟶ NU := (Over.pullback a).map gm
  let : LocallyOfFiniteType MU.hom := by
    dsimp [MU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MU.hom := by
    dsimp [MU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : IsSeparated MU.hom := by
    dsimp [MU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : IsSeparated NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : Smooth gmU.left := MorphismProperty.overPullbackMap (P := @Smooth) a gm hgm.1
  let : GeometricallyConnected gmU.left :=
    MorphismProperty.overPullbackMap (P := @GeometricallyConnected) a gm hgm.2
  let eMU := curveGenericFiberCompIso k F T.val M U.property
  let eNU := curveGenericFiberCompIso k F T.val N U.property
  let eU := eMU ≪≫ eT
  let fU := eNU ≪≫ fT
  let pT := Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F T.val).subtype)
  let pU := Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U.val).subtype)
  have hnU : (Over.pullback pU).map gmU ≫ eNU.hom =
      eMU.hom ≫ (Over.pullback pT).map gm :=
    pullbackComp_naturality a pU pT (by rw [← Spec.map_comp]; rfl) M N gm
  have hmU : (Over.pullback pU).map gmU ≫ fU.hom = eU.hom ≫ g := by
    simp only [eU, fU, Iso.trans_hom, Category.assoc]
    rw [← hm, reassoc_of% hnU]
  have hX := curvePlaceSpreadTopologyIndependence k F S U.val X MU Y e eU
  have hZ := curvePlaceSpreadTopologyIndependence k F V U.val Z NU W f fU
  rw [hX, hZ]
  exact curve_spread_open_of_model k F hLW hsurj hloc hred U.val MU NU Y W eU fU g gmU hmU

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- Fixed-model full-adele openness at a level whose actual integer ring is of
finite type over the integers. -/
private lemma number_fixedModel_open
    (hLW : Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u})
    (hsurj : NumberFieldLevelComponentSurjectivityStatement.{u})
    (hloc : NumberFieldSmoothLocalPointOpenStatement.{u})
    (hred : NumberFieldFixedModelAdeleOpenOfLocalStatement.{u})
    (S : Finset (FinitePlace K))
    [Algebra.FiniteType ℤ ((S : Set (FinitePlace K)).integer K)]
    (M N : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom] [IsSeparated M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] [IsSeparated N.hom]
    (gm : M ⟶ N) [Smooth gm.left] [GeometricallyConnected gm.left] :
    @IsOpenMap _ _ (numberFieldFixedModelAdelePointTopology K S M)
      (numberFieldFixedModelAdelePointTopology K S N)
      (fun p : NumberFieldFixedModelAdelePoints K S M => p ≫ gm) := by
  obtain ⟨hsep, hqc⟩ := over_hom_separated_quasiCompact gm
  refine hred K S M N gm (fun T i => hloc K S M N gm T i) ?_
  exact hsurj hLW K S N M gm
    (locallyOfFiniteType_toSpecULiftZ_of_over ((S : Set (FinitePlace K)).integer K) N)
    (QuasiCompact.compactSpace_of_compactSpace N.hom) inferInstance hsep hqc inferInstance

/-- Openness for the full-adele spread topologies of compatible models. -/
private lemma number_spread_open_of_model
    (hLW : Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u})
    (hsurj : NumberFieldLevelComponentSurjectivityStatement.{u})
    (hloc : NumberFieldSmoothLocalPointOpenStatement.{u})
    (hred : NumberFieldFixedModelAdeleOpenOfLocalStatement.{u})
    (S : Finset (FinitePlace K))
    [Algebra.FiniteType ℤ ((S : Set (FinitePlace K)).integer K)]
    (M N : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType M.hom] [QuasiCompact M.hom] [IsSeparated M.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom] [IsSeparated N.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S M ≅ Y)
    (f : numberFieldModelGenericFiber K S N ≅ W)
    (g : Y ⟶ W) (gm : M ⟶ N) [Smooth gm.left] [GeometricallyConnected gm.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom
          ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map gm ≫
        f.hom = e.hom ≫ g) :
    @IsOpenMap (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S M Y e)
      (numberFieldSpreadAdelePointTopology K S N W f)
      (fun p => p ≫ g) := by
  let := numberFieldFixedModelAdelePointTopology K S M
  let := numberFieldFixedModelAdelePointTopology K S N
  let := numberFieldSpreadAdelePointTopology K S M Y e
  let := numberFieldSpreadAdelePointTopology K S N W f
  let eM := numberFieldSpreadAdelePointHomeomorph K S M Y e
  let eN := numberFieldSpreadAdelePointHomeomorph K S N W f
  have hn (p : NumberFieldFixedModelAdelePoints K S M) :
      eN (p ≫ gm) = eM p ≫ g := by
    change numberFieldGenericFiberAdelePointEquiv K S N (p ≫ gm) ≫ f.hom =
      (numberFieldGenericFiberAdelePointEquiv K S M p ≫ e.hom) ≫ g
    rw [numberFieldGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => numberFieldGenericFiberAdelePointEquiv K S M p ≫ q) h
  have hc := eN.isOpenMap.comp
    ((number_fixedModel_open K hLW hsurj hloc hred S M N gm).comp eM.symm.isOpenMap)
  have heq : (fun p => p ≫ g) = (eN ∘ (fun p => p ≫ gm) ∘ eM.symm) := by
    funext p
    change p ≫ g = eN (eM.symm p ≫ gm)
    rw [hn, eM.apply_symm_apply]
  exact heq.symm ▸ hc

/-- The generic fibre of a number-field model pulled back to a larger level. -/
private def numberGenericFiberCompIso (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    {U : Finset (FinitePlace K)} (hSU : S ⊆ U) :
    numberFieldModelGenericFiber K U (numberFieldLevelModelBaseChange K hSU X) ≅
      numberFieldModelGenericFiber K S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))
    (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) X

end NumberField

/-- Number fields: assembly of Conrad's Theorem 4.5 from its inputs. -/
theorem numberFieldSpreadSmoothOpenAssembly :
    NumberFieldSpreadSmoothOpenAssemblyStatement.{u} := by
  intro hLW hsurj hloc hred hmodel K _ _ S V X Z _ _ _ _ Y W _ _ e f g _ _ _
  let : LocallyOfFiniteType (numberFieldModelGenericFiber K S X).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : QuasiCompact (numberFieldModelGenericFiber K S X).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType (numberFieldModelGenericFiber K V Z).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : QuasiCompact (numberFieldModelGenericFiber K V Z).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType Y.hom := by
    rw [← Over.w e.inv]
    infer_instance
  let : QuasiCompact Y.hom := by
    rw [← Over.w e.inv]
    infer_instance
  let : LocallyOfFiniteType W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  let : QuasiCompact W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  obtain ⟨T, M, N, hMft, hMqc, hMsep, hNft, hNqc, hNsep, eT, fT, gm, hgm, hm⟩ :=
    hmodel K S Y W g ⟨inferInstance, inferInstance⟩
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  let U := numberFieldPrincipalLevelAbove K T.val
  let : Algebra.FiniteType ℤ ((U.val : Set (FinitePlace K)).integer K) :=
    numberFieldPrincipalLevelAbove_finiteType K T.val
  let a := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K U.property))
  let MU := numberFieldLevelModelBaseChange K U.property M
  let NU := numberFieldLevelModelBaseChange K U.property N
  let gmU : MU ⟶ NU := (Over.pullback a).map gm
  let : LocallyOfFiniteType MU.hom := by
    dsimp [MU, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact MU.hom := by
    dsimp [MU, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsSeparated MU.hom := by
    dsimp [MU, numberFieldLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsSeparated NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let : Smooth gmU.left := MorphismProperty.overPullbackMap (P := @Smooth) a gm hgm.1
  let : GeometricallyConnected gmU.left :=
    MorphismProperty.overPullbackMap (P := @GeometricallyConnected) a gm hgm.2
  let eMU := numberGenericFiberCompIso K T.val M U.property
  let eNU := numberGenericFiberCompIso K T.val N U.property
  let eU := eMU ≪≫ eT
  let fU := eNU ≪≫ fT
  let pT := Spec.map (CommRingCat.ofHom
    ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype)
  let pU := Spec.map (CommRingCat.ofHom
    ((U.val : Set (FinitePlace K)).integer K).toSubring.subtype)
  have hnU : (Over.pullback pU).map gmU ≫ eNU.hom =
      eMU.hom ≫ (Over.pullback pT).map gm :=
    pullbackComp_naturality a pU pT (by rw [← Spec.map_comp]; rfl) M N gm
  have hmU : (Over.pullback pU).map gmU ≫ fU.hom = eU.hom ≫ g := by
    simp only [eU, fU, Iso.trans_hom, Category.assoc]
    rw [← hm, reassoc_of% hnU]
  have hX := numberFieldSpreadTopologyIndependence K S U.val X MU Y e eU
  have hZ := numberFieldSpreadTopologyIndependence K V U.val Z NU W f fU
  rw [hX, hZ]
  exact number_spread_open_of_model K hLW hsurj hloc hred U.val MU NU Y W eU fU g gmU hmU

/-- Conrad's Theorem 4.5 in both characteristics from its separately stated inputs. -/
theorem adelicSpreadSmoothOpenAssembly : AdelicSpreadSmoothOpenAssemblyStatement.{u} :=
  ⟨curvePlaceSpreadSmoothOpenAssembly, numberFieldSpreadSmoothOpenAssembly⟩

end Langlands.Global
