import Langlands.Global.AdelicSpreadModelMorphisms
import Langlands.Global.AdelicSpreadClosedImmersionStatement
import Langlands.Global.AdelicFixedModelClosedImmersionProof
import Langlands.AlgebraicGeometry.SchemeFilteredClosedImmersionProof
import Langlands.Global.AdelicSpreadTopologyIndependenceProof
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.Global.AdelicFixedModelInitialSetTopologyProof
import Langlands.Global.AdelicFixedModelFunctorialityProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Closed embeddings on actual adelic generic-fiber points -/

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

open EtaleEquivalenceRelation.Action.TargetLimit AffineLimit
open SchemeLimitModel

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {B : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj B)
  (c : Cone D) (p : c.pt ⟶ B)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)
  (X : Over B)

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
  (hc : IsLimit c) (Z : Over B)

omit [IsCofiltered I] [∀ i, IsAffine (D.obj i)] in
private lemma modelConeLeg_closed (i : I)
    (f : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Z)
    [IsClosedImmersion f.left]
    (fi : (Over.pullback (t.app i)).obj X ⟶ (Over.pullback (t.app i)).obj Z)
    (h : modelConeLeg D t c p hp X i ≫ fi.left =
      f.left ≫ modelConeLeg D t c p hp Z i) :
    IsClosedImmersion ((Over.pullback (c.π.app i)).map fi).left := by
  have hn := modelConeLeg_naturality D t c p hp X Z i f fi h
  have heq : (Over.pullback (c.π.app i)).map fi =
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) X).hom ≫ f ≫
        (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) Z).inv := by
    apply (cancel_mono
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) Z).hom).mp
    simpa using hn
  rw [heq, Over.comp_left, Over.comp_left]
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.PointTopology

open AffineLimit

private lemma pullbackMap_closed_iff {B T : Scheme.{u}}
    (X Z : Over B) (f : X ⟶ Z) (p : T ⟶ B) :
    IsClosedImmersion (baseChangeMap X.hom Z.hom f.left (Over.w f) p) ↔
      IsClosedImmersion ((Over.pullback p).map f).left := by
  have h : baseChangeMap X.hom Z.hom f.left (Over.w f) p =
      (pullbackSymmetry p X.hom).hom ≫ ((Over.pullback p).map f).left ≫
        (pullbackSymmetry Z.hom p).hom := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [h]
  exact MorphismProperty.cancel_left_of_respectsIso _ _ _ |>.trans
    (MorphismProperty.cancel_right_of_respectsIso _ _ _)

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

private def curveGenericFiberCompIso {U : Finset (AlgebraicCurve.Place k F)}
    (hSU : S ⊆ U) :
    curvePlaceModelGenericFiber k F U (curvePlaceLevelModelBaseChange k F hSU X) ≅
      curvePlaceModelGenericFiber k F S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) X

private lemma curve_spread_closed_of_model
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ W)
    (g : Y ⟶ W) (fi : X ⟶ Z) [IsClosedImmersion fi.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map fi ≫
        f.hom = e.hom ≫ g) :
    @IsClosedEmbedding (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)
      (curvePlaceSpreadAdelePointTopology k F S Z W f)
      (fun p => p ≫ g) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Z
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceSpreadAdelePointTopology k F S Z W f
  let eX := curvePlaceSpreadAdelePointHomeomorph k F S X Y e
  let eZ := curvePlaceSpreadAdelePointHomeomorph k F S Z W f
  have hn (p : CurvePlaceFixedModelAdelePoints k F S X) :
      eZ (p ≫ fi) = eX p ≫ g := by
    change curvePlaceGenericFiberAdelePointEquiv k F S Z (p ≫ fi) ≫ f.hom =
      (curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ e.hom) ≫ g
    rw [curvePlaceGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ q) h
  have hc := eZ.isClosedEmbedding.comp
    ((curvePlaceFixedModelAdele_isClosedEmbedding k F S fi).comp
      eX.symm.isClosedEmbedding)
  convert hc using 1
  funext p
  change p ≫ g = eZ (eX.symm p ≫ fi)
  rw [hn, eX.apply_symm_apply]

private lemma curve_spread_closed_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ W)
    (g : Y ⟶ W) [IsClosedImmersion g.left] :
    @IsClosedEmbedding (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)
      (curvePlaceSpreadAdelePointTopology k F S Z W f)
      (fun p => p ≫ g) := by
  let eg := e.hom ≫ g ≫ f.inv
  let : IsClosedImmersion eg.left := by dsimp [eg]; infer_instance
  obtain ⟨T, fi, hdesc⟩ := curve_exists_modelMorphism k F S X Z eg
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let ZT := curvePlaceLevelModelBaseChange k F T.property Z
  let pT := Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F T.val).subtype)
  let egT : curvePlaceModelGenericFiber k F T.val XT ⟶
      curvePlaceModelGenericFiber k F T.val ZT := (Over.pullback pT).map fi
  have hgT : IsClosedImmersion egT.left :=
    modelConeLeg_closed (curveIntegerD k F S) (curveIntegerT k F S)
      (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S)
      X Z (op T) eg fi hdesc
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZT.hom := by
    dsimp [ZT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZT.hom := by
    dsimp [ZT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : IsNoetherianRing (curvePlaceSIntegers k F T.val) :=
    (adelicSIntegersNoetherian.1 k F T.val).1
  let : IsLocallyNoetherian XT.left := LocallyOfFiniteType.isLocallyNoetherian XT.hom
  let : IsLocallyNoetherian ZT.left := LocallyOfFiniteType.isLocallyNoetherian ZT.hom
  have : LocallyOfFiniteType (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : QuasiCompact (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : QuasiSeparated (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : LocallyOfFiniteType fi.left := locallyOfFiniteType_of_comp fi.left ZT.hom
  have : QuasiCompact fi.left := QuasiCompact.of_comp fi.left ZT.hom
  have : QuasiSeparated fi.left := QuasiSeparated.of_comp fi.left ZT.hom
  have hbase := (pullbackMap_closed_iff XT ZT fi pT).2 hgT
  obtain ⟨U, hU⟩ := (spectrumClosedImmersionDescent
    (curvePlaceSIntegers k F T.val) (curvePlaceSIntegersOverDiagram k F T.val)
    (curvePlaceSIntegersOverCocone k F T.val) (curvePlaceSIntegersOverIsColimit k F T.val)
    XT ZT fi).mp hbase
  let a := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F U.property))
  let XU := curvePlaceLevelModelBaseChange k F U.property XT
  let ZU := curvePlaceLevelModelBaseChange k F U.property ZT
  let fiU : XU ⟶ ZU := (Over.pullback a).map fi
  let : IsClosedImmersion fiU.left := (pullbackMap_closed_iff XT ZT fi a).1 hU
  let : LocallyOfFiniteType XU.hom := by
    dsimp [XU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XU.hom := by
    dsimp [XU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZU.hom := by
    dsimp [ZU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZU.hom := by
    dsimp [ZU, curvePlaceLevelModelBaseChange]
    infer_instance
  let eTX := curveGenericFiberCompIso k F S X T.property
  let eTZ := curveGenericFiberCompIso k F S Z T.property
  let eUX := curveGenericFiberCompIso k F T.val XT U.property
  let eUZ := curveGenericFiberCompIso k F T.val ZT U.property
  let eU := eUX ≪≫ eTX ≪≫ e
  let fU := eUZ ≪≫ eTZ ≪≫ f
  have hnT : egT ≫ eTZ.hom = eTX.hom ≫ eg :=
    modelConeLeg_naturality (curveIntegerD k F S) (curveIntegerT k F S)
      (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S)
      X Z (op T) eg fi hdesc
  let pU := Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U.val).subtype)
  have hnU : (Over.pullback pU).map fiU ≫ eUZ.hom = eUX.hom ≫ egT :=
    pullbackComp_naturality a pU pT (by rw [← Spec.map_comp]; rfl) XT ZT fi
  have hm : (Over.pullback pU).map fiU ≫ fU.hom = eU.hom ≫ g := by
    have h₁ := congrArg (fun q => q ≫ eTZ.hom ≫ f.hom) hnU
    have h₂ := congrArg (fun q => eUX.hom ≫ q ≫ f.hom) hnT
    simp only [Category.assoc] at h₁ h₂
    simpa [eU, fU, eg] using h₁.trans h₂
  have hX := curvePlaceSpreadTopologyIndependence k F S U.val X XU Y e eU
  have hZ := curvePlaceSpreadTopologyIndependence k F S U.val Z ZU W f fU
  rw [hX, hZ]
  exact curve_spread_closed_of_model k F U.val XU ZU Y W eU fU g fiU hm

end Curve

/-- Closed immersions give closed embeddings for arbitrary function-field spreads. -/
theorem curvePlaceSpreadClosedImmersion : CurvePlaceSpreadClosedImmersionStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U X Z _ _ _ _ Y W e f g _
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
  exact curve_spread_closed_sameBase k F V XV ZV Y W _ _ g

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

private def numberGenericFiberCompIso {U : Finset (FinitePlace K)}
    (hSU : S ⊆ U) :
    numberFieldModelGenericFiber K U (numberFieldLevelModelBaseChange K hSU X) ≅
      numberFieldModelGenericFiber K S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))
    (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) X

private lemma number_spread_closed_of_model
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ W)
    (g : Y ⟶ W) (fi : X ⟶ Z) [IsClosedImmersion fi.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map fi ≫
        f.hom = e.hom ≫ g) :
    @IsClosedEmbedding (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S X Y e)
      (numberFieldSpreadAdelePointTopology K S Z W f)
      (fun p => p ≫ g) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Z
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldSpreadAdelePointTopology K S Z W f
  let eX := numberFieldSpreadAdelePointHomeomorph K S X Y e
  let eZ := numberFieldSpreadAdelePointHomeomorph K S Z W f
  have hn (p : NumberFieldFixedModelAdelePoints K S X) :
      eZ (p ≫ fi) = eX p ≫ g := by
    change numberFieldGenericFiberAdelePointEquiv K S Z (p ≫ fi) ≫ f.hom =
      (numberFieldGenericFiberAdelePointEquiv K S X p ≫ e.hom) ≫ g
    rw [numberFieldGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => numberFieldGenericFiberAdelePointEquiv K S X p ≫ q) h
  have hc := eZ.isClosedEmbedding.comp
    ((numberFieldFixedModelAdele_isClosedEmbedding K S fi).comp
      eX.symm.isClosedEmbedding)
  convert hc using 1
  funext p
  change p ≫ g = eZ (eX.symm p ≫ fi)
  rw [hn, eX.apply_symm_apply]

private lemma number_spread_closed_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ W)
    (g : Y ⟶ W) [IsClosedImmersion g.left] :
    @IsClosedEmbedding (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S X Y e)
      (numberFieldSpreadAdelePointTopology K S Z W f)
      (fun p => p ≫ g) := by
  let eg := e.hom ≫ g ≫ f.inv
  let : IsClosedImmersion eg.left := by dsimp [eg]; infer_instance
  obtain ⟨T, fi, hdesc⟩ := number_exists_modelMorphism K S X Z eg
  let XT := numberFieldLevelModelBaseChange K T.property X
  let ZT := numberFieldLevelModelBaseChange K T.property Z
  let pT := Spec.map (CommRingCat.ofHom ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype)
  let egT : numberFieldModelGenericFiber K T.val XT ⟶
      numberFieldModelGenericFiber K T.val ZT := (Over.pullback pT).map fi
  have hgT : IsClosedImmersion egT.left :=
    modelConeLeg_closed (numberIntegerD K S) (numberIntegerT K S)
      (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S)
      X Z (op T) eg fi hdesc
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZT.hom := by
    dsimp [ZT, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZT.hom := by
    dsimp [ZT, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsNoetherianRing ((T.val : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K T.val).1
  let : IsLocallyNoetherian XT.left := LocallyOfFiniteType.isLocallyNoetherian XT.hom
  let : IsLocallyNoetherian ZT.left := LocallyOfFiniteType.isLocallyNoetherian ZT.hom
  have : LocallyOfFiniteType (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : QuasiCompact (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : QuasiSeparated (fi.left ≫ ZT.hom) := by rw [Over.w fi]; infer_instance
  have : LocallyOfFiniteType fi.left := locallyOfFiniteType_of_comp fi.left ZT.hom
  have : QuasiCompact fi.left := QuasiCompact.of_comp fi.left ZT.hom
  have : QuasiSeparated fi.left := QuasiSeparated.of_comp fi.left ZT.hom
  have hbase := (pullbackMap_closed_iff XT ZT fi pT).2 hgT
  obtain ⟨U, hU⟩ := (spectrumClosedImmersionDescent
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldSIntegersOverDiagram K T.val)
    (numberFieldSIntegersOverCocone K T.val) (numberFieldSIntegersOverIsColimit K T.val)
    XT ZT fi).mp hbase
  let a := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K U.property))
  let XU := numberFieldLevelModelBaseChange K U.property XT
  let ZU := numberFieldLevelModelBaseChange K U.property ZT
  let fiU : XU ⟶ ZU := (Over.pullback a).map fi
  let : IsClosedImmersion fiU.left := (pullbackMap_closed_iff XT ZT fi a).1 hU
  let : LocallyOfFiniteType XU.hom := by
    dsimp [XU, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XU.hom := by
    dsimp [XU, numberFieldLevelModelBaseChange]
    infer_instance
  let : LocallyOfFiniteType ZU.hom := by
    dsimp [ZU, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact ZU.hom := by
    dsimp [ZU, numberFieldLevelModelBaseChange]
    infer_instance
  let eTX := numberGenericFiberCompIso K S X T.property
  let eTZ := numberGenericFiberCompIso K S Z T.property
  let eUX := numberGenericFiberCompIso K T.val XT U.property
  let eUZ := numberGenericFiberCompIso K T.val ZT U.property
  let eU := eUX ≪≫ eTX ≪≫ e
  let fU := eUZ ≪≫ eTZ ≪≫ f
  have hnT : egT ≫ eTZ.hom = eTX.hom ≫ eg :=
    modelConeLeg_naturality (numberIntegerD K S) (numberIntegerT K S)
      (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S)
      X Z (op T) eg fi hdesc
  let pU := Spec.map (CommRingCat.ofHom ((U.val : Set (FinitePlace K)).integer K).toSubring.subtype)
  have hnU : (Over.pullback pU).map fiU ≫ eUZ.hom = eUX.hom ≫ egT :=
    pullbackComp_naturality a pU pT (by rw [← Spec.map_comp]; rfl) XT ZT fi
  have hm : (Over.pullback pU).map fiU ≫ fU.hom = eU.hom ≫ g := by
    have h₁ := congrArg (fun q => q ≫ eTZ.hom ≫ f.hom) hnU
    have h₂ := congrArg (fun q => eUX.hom ≫ q ≫ f.hom) hnT
    simp only [Category.assoc] at h₁ h₂
    simpa [eU, fU, eg] using h₁.trans h₂
  have hX := numberFieldSpreadTopologyIndependence K S U.val X XU Y e eU
  have hZ := numberFieldSpreadTopologyIndependence K S U.val Z ZU W f fU
  rw [hX, hZ]
  exact number_spread_closed_of_model K U.val XU ZU Y W eU fU g fiU hm

end NumberField

/-- Closed immersions give closed embeddings for arbitrary number-field spreads. -/
theorem numberFieldSpreadClosedImmersion : NumberFieldSpreadClosedImmersionStatement.{u} := by
  intro K _ _ S U X Z _ _ _ _ Y W e f g _
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
  exact number_spread_closed_sameBase K V XV ZV Y W _ _ g

/-- The exact two-arithmetic-case closed-embedding target. -/
theorem adelicSpreadClosedImmersion : AdelicSpreadClosedImmersionStatement.{u} :=
  ⟨curvePlaceSpreadClosedImmersion, numberFieldSpreadClosedImmersion⟩

end Langlands.Global
