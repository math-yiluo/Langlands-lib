import Langlands.Global.AdelicSpreadModelMorphisms
import Langlands.Global.AdelicSpreadFunctorialityStatement
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.Global.AdelicFixedModelInitialSetTopologyProof
import Langlands.Global.AdelicFixedModelFunctorialityProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Functoriality of actual adelic generic-fiber points -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Topology Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms

namespace Langlands.AlgebraicGeometry.PointTopology

private def equivHomeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ B) (he : IsHomeomorph e) : A ≃ₜ B where
  toEquiv := e
  continuous_toFun := he.continuous
  continuous_invFun := e.continuous_symm_iff.2 he.isOpenMap

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.SchemeLimitModel

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [PerfectField k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))

private abbrev curveIntegerD :=
  spectrumDiagram (curvePlaceSIntegers k F S) (curvePlaceSIntegersOverDiagram k F S)
private abbrev curveIntegerT :=
  spectrumStructure (curvePlaceSIntegers k F S) (curvePlaceSIntegersOverDiagram k F S)
private abbrev curveIntegerC :=
  spectrumCone (curvePlaceSIntegers k F S) (curvePlaceSIntegersOverDiagram k F S)
    (curvePlaceSIntegersOverCocone k F S)
private abbrev curveIntegerP :=
  spectrumBaseMap (curvePlaceSIntegers k F S) (curvePlaceSIntegersOverDiagram k F S)
    (curvePlaceSIntegersOverCocone k F S)
private abbrev curveIntegerW :=
  spectrumCone_compat (curvePlaceSIntegers k F S) (curvePlaceSIntegersOverDiagram k F S)
    (curvePlaceSIntegersOverCocone k F S)

variable (X Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

private abbrev curveGenericLeg (T : AdelicLevelIndexAbove S) :=
  modelConeLeg (curveIntegerD k F S) (curveIntegerT k F S)
    (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S) X (op T)

private lemma curve_exists_modelMorphism
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : curvePlaceModelGenericFiber k F S X ⟶ curvePlaceModelGenericFiber k F S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (fi : curvePlaceLevelModelBaseChange k F T.property X ⟶
        curvePlaceLevelModelBaseChange k F T.property Z),
      curveGenericLeg k F S X T ≫ fi.left =
        f.left ≫ curveGenericLeg k F S Z T := by
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hc := spectrumConeIsLimit (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S)
  obtain ⟨i, fi, h⟩ := exists_modelMorphism (curveIntegerD k F S) (curveIntegerT k F S)
    (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S) X hc Z f
  exact ⟨i.unop, fi, h⟩

private lemma curve_genericLeg_point (T : AdelicLevelIndexAbove S)
    (p : CurvePlaceFixedModelAdelePoints k F S X) :
    (curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
        curveGenericLeg k F S X T =
      (curvePlaceFixedModelInitialSetEquiv k F T.property X p).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, modelConeLeg_fst]
    change (curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) =
      (curvePlaceFixedModelInitialSetEquiv k F T.property X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))
    rw [curvePlaceGenericFiberAdelePointEquiv_left_fst,
      curvePlaceFixedModelInitialSetEquiv_left_fst]
  · rw [Category.assoc, modelConeLeg_snd, ← Category.assoc]
    change ((curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
        (curvePlaceModelGenericFiber k F S X).hom) ≫ _ =
      (curvePlaceFixedModelInitialSetEquiv k F T.property X p).left ≫
        (curvePlaceLevelModelBaseChange k F T.property X).hom
    rw [Over.w, Over.w]
    change Spec.map (CommRingCat.ofHom (curvePlaceAdeleDiagonal k F)) ≫
      Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F T.val).subtype) =
      Spec.map (CommRingCat.ofHom
        ((curvePlaceAdeleLevel k F T.val).subtype.comp
          (curvePlaceAdeleLevelDiagonal k F T.val)))
    rw [← Spec.map_comp]
    congr 1

private lemma curve_spread_continuous_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ W)
    (g : Y ⟶ W) :
    Continuous[curvePlaceSpreadAdelePointTopology k F S X Y e,
      curvePlaceSpreadAdelePointTopology k F S Z W f]
      (fun p : CurvePlaceAdelePoints k F Y => (p ≫ g : CurvePlaceAdelePoints k F W)) := by
  let eg := e.hom ≫ g ≫ f.inv
  obtain ⟨T, fi, hdesc⟩ := curve_exists_modelMorphism k F S X Z eg
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Z
  let := curvePlaceFixedModelAdelePointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  let := curvePlaceFixedModelAdelePointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property Z)
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceSpreadAdelePointTopology k F S Z W f
  let hX := equivHomeomorph (curvePlaceFixedModelInitialSetEquiv k F T.property X)
    (curvePlaceFixedModelInitialSetTopology k F S T.val T.property X)
  let hZ := equivHomeomorph (curvePlaceFixedModelInitialSetEquiv k F T.property Z)
    (curvePlaceFixedModelInitialSetTopology k F S T.val T.property Z)
  let h : CurvePlaceFixedModelAdelePoints k F S X →
      CurvePlaceFixedModelAdelePoints k F S Z := fun p => hZ.symm (hX p ≫ fi)
  have hcont : Continuous h :=
    hZ.symm.continuous.comp
      ((curvePlaceFixedModelAdele_continuous k F T.val fi).comp hX.continuous)
  have hstage (p : CurvePlaceFixedModelAdelePoints k F S X) :
      curvePlaceFixedModelInitialSetEquiv k F T.property Z (h p) =
        curvePlaceFixedModelInitialSetEquiv k F T.property X p ≫ fi :=
    (curvePlaceFixedModelInitialSetEquiv k F T.property Z).apply_symm_apply _
  have hgeneric (p : CurvePlaceFixedModelAdelePoints k F S X) :
      curvePlaceGenericFiberAdelePointEquiv k F S Z (h p) =
        curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ eg := by
    apply (curvePlaceGenericFiberAdelePointEquiv k F S Z).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [curvePlaceGenericFiberAdelePointEquiv_symm_left]
    change (h p).left = ((curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
      eg.left) ≫ pullback.fst Z.hom (curveIntegerP k F S)
    calc
      _ = (curvePlaceFixedModelInitialSetEquiv k F T.property Z (h p)).left ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) :=
        (curvePlaceFixedModelInitialSetEquiv_left_fst k F T.property Z (h p)).symm
      _ = ((curvePlaceFixedModelInitialSetEquiv k F T.property X p).left ≫ fi.left) ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) := by rw [hstage]; rfl
      _ = (((curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
          curveGenericLeg k F S X T) ≫ fi.left) ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) := by
        rw [curve_genericLeg_point]
      _ = _ := by
        simp only [Category.assoc]
        rw [← Category.assoc (curveGenericLeg k F S X T), hdesc]
        simp only [Category.assoc, modelConeLeg_fst]
  let eX := curvePlaceSpreadAdelePointHomeomorph k F S X Y e
  let eZ := curvePlaceSpreadAdelePointHomeomorph k F S Z W f
  have hspread (p : CurvePlaceFixedModelAdelePoints k F S X) :
      eZ (h p) = eX p ≫ g := by
    change curvePlaceGenericFiberAdelePointEquiv k F S Z (h p) ≫ f.hom =
      (curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ e.hom) ≫ g
    rw [hgeneric]
    simp [eg]
  refine (eZ.continuous.comp (hcont.comp eX.symm.continuous)).congr ?_
  intro p
  change eZ (h (eX.symm p)) = p ≫ g
  rw [hspread, eX.apply_symm_apply]

private def curveGenericFiberCompIso {U : Finset (AlgebraicCurve.Place k F)}
    (hSU : S ⊆ U) :
    curvePlaceModelGenericFiber k F U (curvePlaceLevelModelBaseChange k F hSU X) ≅
      curvePlaceModelGenericFiber k F S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) X

end Curve

/-- Actual postcomposition is continuous for arbitrary function-field spreads. -/
theorem curvePlaceSpreadFunctoriality : CurvePlaceSpreadFunctorialityStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U X Z _ _ _ _ Y W e f g
  classical
  let V := S ∪ U
  have hSV : S ⊆ V := Finset.subset_union_left
  have hUV : U ⊆ V := Finset.subset_union_right
  let XV := curvePlaceLevelModelBaseChange k F hSV X
  let ZV := curvePlaceLevelModelBaseChange k F hUV Z
  let : LocallyOfFiniteType XV.hom := by
    dsimp [XV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XV.hom := by
    dsimp [XV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZV.hom := by
    dsimp [ZV, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZV.hom := by
    dsimp [ZV, curvePlaceLevelModelBaseChange]
    infer_instance
  have hX := curvePlaceSpreadTopologyIndependence k F S V X XV Y e
    (curveGenericFiberCompIso k F S X hSV ≪≫ e)
  have hZ := curvePlaceSpreadTopologyIndependence k F U V Z ZV W f
    (curveGenericFiberCompIso k F U Z hUV ≪≫ f)
  rw [hX, hZ]
  exact curve_spread_continuous_sameBase k F V XV ZV Y W _ _ g

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

private abbrev numberIntegerD :=
  spectrumDiagram ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K S)
private abbrev numberIntegerT :=
  spectrumStructure ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K S)
private abbrev numberIntegerC :=
  spectrumCone ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K S)
    (numberFieldSIntegersOverCocone K S)
private abbrev numberIntegerP :=
  spectrumBaseMap ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K S)
    (numberFieldSIntegersOverCocone K S)
private abbrev numberIntegerW :=
  spectrumCone_compat ((S : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K S)
    (numberFieldSIntegersOverCocone K S)

variable (X Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

private abbrev numberGenericLeg (T : AdelicLevelIndexAbove S) :=
  modelConeLeg (numberIntegerD K S) (numberIntegerT K S)
    (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S) X (op T)

private lemma number_exists_modelMorphism
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : numberFieldModelGenericFiber K S X ⟶ numberFieldModelGenericFiber K S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (fi : numberFieldLevelModelBaseChange K T.property X ⟶
        numberFieldLevelModelBaseChange K T.property Z),
      numberGenericLeg K S X T ≫ fi.left =
        f.left ≫ numberGenericLeg K S Z T := by
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hc := spectrumConeIsLimit ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S)
  obtain ⟨i, fi, h⟩ := exists_modelMorphism (numberIntegerD K S) (numberIntegerT K S)
    (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S) X hc Z f
  exact ⟨i.unop, fi, h⟩

private lemma number_genericLeg_point (T : AdelicLevelIndexAbove S)
    (p : NumberFieldFixedModelAdelePoints K S X) :
    (numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
        numberGenericLeg K S X T =
      (numberFieldFixedModelInitialSetEquiv K T.property X p).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, modelConeLeg_fst]
    change (numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) =
      (numberFieldFixedModelInitialSetEquiv K T.property X p).left ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))
    rw [numberFieldGenericFiberAdelePointEquiv_left_fst,
      numberFieldFixedModelInitialSetEquiv_left_fst]
  · rw [Category.assoc, modelConeLeg_snd, ← Category.assoc]
    change ((numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
        (numberFieldModelGenericFiber K S X).hom) ≫ _ =
      (numberFieldFixedModelInitialSetEquiv K T.property X p).left ≫
        (numberFieldLevelModelBaseChange K T.property X).hom
    rw [Over.w, Over.w]
    change Spec.map (CommRingCat.ofHom (diagonal K)) ≫
      Spec.map (CommRingCat.ofHom ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype) =
      Spec.map (CommRingCat.ofHom
        ((numberFieldAdeleLevel K T.val).subtype.comp
          (numberFieldAdeleLevelDiagonal K T.val)))
    rw [← Spec.map_comp]
    congr 1

private lemma number_spread_continuous_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ W)
    (g : Y ⟶ W) :
    Continuous[numberFieldSpreadAdelePointTopology K S X Y e,
      numberFieldSpreadAdelePointTopology K S Z W f]
      (fun p : NumberFieldAdelePoints K Y => (p ≫ g : NumberFieldAdelePoints K W)) := by
  let eg := e.hom ≫ g ≫ f.inv
  obtain ⟨T, fi, hdesc⟩ := number_exists_modelMorphism K S X Z eg
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Z
  let := numberFieldFixedModelAdelePointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  let := numberFieldFixedModelAdelePointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property Z)
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldSpreadAdelePointTopology K S Z W f
  let hX := equivHomeomorph (numberFieldFixedModelInitialSetEquiv K T.property X)
    (numberFieldFixedModelInitialSetTopology K S T.val T.property X)
  let hZ := equivHomeomorph (numberFieldFixedModelInitialSetEquiv K T.property Z)
    (numberFieldFixedModelInitialSetTopology K S T.val T.property Z)
  let h : NumberFieldFixedModelAdelePoints K S X →
      NumberFieldFixedModelAdelePoints K S Z := fun p => hZ.symm (hX p ≫ fi)
  have hcont : Continuous h :=
    hZ.symm.continuous.comp
      ((numberFieldFixedModelAdele_continuous K T.val fi).comp hX.continuous)
  have hstage (p : NumberFieldFixedModelAdelePoints K S X) :
      numberFieldFixedModelInitialSetEquiv K T.property Z (h p) =
        numberFieldFixedModelInitialSetEquiv K T.property X p ≫ fi :=
    (numberFieldFixedModelInitialSetEquiv K T.property Z).apply_symm_apply _
  have hgeneric (p : NumberFieldFixedModelAdelePoints K S X) :
      numberFieldGenericFiberAdelePointEquiv K S Z (h p) =
        numberFieldGenericFiberAdelePointEquiv K S X p ≫ eg := by
    apply (numberFieldGenericFiberAdelePointEquiv K S Z).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [numberFieldGenericFiberAdelePointEquiv_symm_left]
    change (h p).left = ((numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
      eg.left) ≫ pullback.fst Z.hom (numberIntegerP K S)
    calc
      _ = (numberFieldFixedModelInitialSetEquiv K T.property Z (h p)).left ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) :=
        (numberFieldFixedModelInitialSetEquiv_left_fst K T.property Z (h p)).symm
      _ = ((numberFieldFixedModelInitialSetEquiv K T.property X p).left ≫ fi.left) ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) := by rw [hstage]; rfl
      _ = (((numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
          numberGenericLeg K S X T) ≫ fi.left) ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) := by
        rw [number_genericLeg_point]
      _ = _ := by
        simp only [Category.assoc]
        rw [← Category.assoc (numberGenericLeg K S X T), hdesc]
        simp only [Category.assoc, modelConeLeg_fst]
  let eX := numberFieldSpreadAdelePointHomeomorph K S X Y e
  let eZ := numberFieldSpreadAdelePointHomeomorph K S Z W f
  have hspread (p : NumberFieldFixedModelAdelePoints K S X) :
      eZ (h p) = eX p ≫ g := by
    change numberFieldGenericFiberAdelePointEquiv K S Z (h p) ≫ f.hom =
      (numberFieldGenericFiberAdelePointEquiv K S X p ≫ e.hom) ≫ g
    rw [hgeneric]
    simp [eg]
  refine (eZ.continuous.comp (hcont.comp eX.symm.continuous)).congr ?_
  intro p
  change eZ (h (eX.symm p)) = p ≫ g
  rw [hspread, eX.apply_symm_apply]

private def numberGenericFiberCompIso {U : Finset (FinitePlace K)}
    (hSU : S ⊆ U) :
    numberFieldModelGenericFiber K U (numberFieldLevelModelBaseChange K hSU X) ≅
      numberFieldModelGenericFiber K S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))
    (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) X

end NumberField

/-- Actual postcomposition is continuous for arbitrary number-field spreads. -/
theorem numberFieldSpreadFunctoriality : NumberFieldSpreadFunctorialityStatement.{u} := by
  intro K _ _ S U X Z _ _ _ _ Y W e f g
  classical
  let V := S ∪ U
  have hSV : S ⊆ V := Finset.subset_union_left
  have hUV : U ⊆ V := Finset.subset_union_right
  let XV := numberFieldLevelModelBaseChange K hSV X
  let ZV := numberFieldLevelModelBaseChange K hUV Z
  let : LocallyOfFiniteType XV.hom := by
    dsimp [XV, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XV.hom := by
    dsimp [XV, numberFieldLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZV.hom := by
    dsimp [ZV, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZV.hom := by
    dsimp [ZV, numberFieldLevelModelBaseChange]
    infer_instance
  have hX := numberFieldSpreadTopologyIndependence K S V X XV Y e
    (numberGenericFiberCompIso K S X hSV ≪≫ e)
  have hZ := numberFieldSpreadTopologyIndependence K U V Z ZV W f
    (numberGenericFiberCompIso K U Z hUV ≪≫ f)
  rw [hX, hZ]
  exact number_spread_continuous_sameBase K V XV ZV Y W _ _ g

/-- The exact two-characteristic target for functoriality of actual adelic points. -/
theorem adelicSpreadFunctoriality : AdelicSpreadFunctorialityStatement.{u} :=
  ⟨curvePlaceSpreadFunctoriality, numberFieldSpreadFunctoriality⟩

end Langlands.Global
