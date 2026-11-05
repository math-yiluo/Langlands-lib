import Langlands.Global.AdelicSpreadTopologyIndependenceStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.Global.AdelicFixedModelInitialSetTopologyProof
import Langlands.Global.AdelicFixedModelFunctorialityProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Independence of the topology from finite-type arithmetic spreads -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Topology Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

private theorem transportedTopology_eq
    {A B Y : Type*} [tA : TopologicalSpace A] [tB : TopologicalSpace B]
    (a : A ≃ Y) (b : B ≃ Y) (h : A ≃ₜ B)
    (w : ∀ x, b (h x) = a x) :
    @Equiv.topologicalSpace _ _ tA a.symm =
      @Equiv.topologicalSpace _ _ tB b.symm := by
  change TopologicalSpace.induced a.symm tA = TopologicalSpace.induced b.symm tB
  calc
    _ = TopologicalSpace.induced a.symm (TopologicalSpace.induced h tB) :=
      congrArg (TopologicalSpace.induced a.symm) h.induced_eq.symm
    _ = TopologicalSpace.induced (h ∘ a.symm) tB :=
      induced_compose
    _ = TopologicalSpace.induced b.symm tB := by
      congr 1
      funext y
      apply b.injective
      rw [Function.comp_apply, w, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private def equivHomeomorph {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ B) (he : IsHomeomorph e) : A ≃ₜ B where
  toEquiv := e
  continuous_toFun := he.continuous
  continuous_invFun := e.continuous_symm_iff.2 he.isOpenMap

@[reassoc (attr := simp)]
private lemma pullbackSymmetry_hom_hom {C : Type*} [Category C]
    {A B D : C} (f : A ⟶ D) (g : B ⟶ D) [HasPullback f g] [HasPullback g f] :
    (pullbackSymmetry f g).hom ≫ (pullbackSymmetry g f).hom = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

open EtaleEquivalenceRelation.Action.TargetLimit AffineLimit
open SchemeLimitModel

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) {B : Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj B)
  (c : Cone D) (p : c.pt ⟶ B)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)
  (X : Over B)

/-- The actual cone projection, with the standard order of model pullbacks. -/
private def modelConeLeg (i : I) :
    ((Over.pullback p).obj X).left ⟶ ((Over.pullback (t.app i)).obj X).left :=
  (pullbackSymmetry X.hom p).hom ≫
    (cone D t X.hom c p hp).π.app i ≫ (pullbackSymmetry (t.app i) X.hom).hom

@[reassoc (attr := simp)]
private lemma modelConeLeg_fst (i : I) :
    modelConeLeg D t c p hp X i ≫ pullback.fst X.hom (t.app i) =
      pullback.fst X.hom p := by
  simp [modelConeLeg]

@[reassoc (attr := simp)]
private lemma modelConeLeg_snd (i : I) :
    modelConeLeg D t c p hp X i ≫ pullback.snd X.hom (t.app i) =
      pullback.snd X.hom p ≫ c.π.app i := by
  simp [modelConeLeg]

variable [IsCofiltered I] [∀ i, IsAffine (D.obj i)]
  (hc : IsLimit c) (Z : Over B)

include hc in
/-- Descend a prescribed actual pullback isomorphism and retain its cone square. -/
private lemma exists_modelIso
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact Z.hom] [QuasiSeparated Z.hom] [LocallyOfFinitePresentation Z.hom]
    (e : (Over.pullback p).obj X ≅ (Over.pullback p).obj Z) :
    ∃ (i : I) (ei : (Over.pullback (t.app i)).obj X ≅ (Over.pullback (t.app i)).obj Z),
      modelConeLeg D t c p hp X i ≫ ei.hom.left =
        e.hom.left ≫ modelConeLeg D t c p hp Z i := by
  let es : pullback p X.hom ≅ pullback p Z.hom :=
    (pullbackSymmetry p X.hom) ≪≫ (Over.forget _).mapIso e ≪≫
      (pullbackSymmetry Z.hom p)
  have hes : es.hom ≫ pullback.fst p Z.hom = pullback.fst p X.hom := by
    simpa [es] using congrArg (fun f => (pullbackSymmetry p X.hom).hom ≫ f) (Over.w e.hom)
  obtain ⟨i, ei, hei, h⟩ :=
    exists_level_isomorphism D t X.hom Z.hom c hc p hp es hes
  let ei' : (Over.pullback (t.app i)).obj X ≅ (Over.pullback (t.app i)).obj Z :=
    Over.isoMk ((pullbackSymmetry X.hom (t.app i)) ≪≫ ei ≪≫
      (pullbackSymmetry (t.app i) Z.hom)) (by
        simpa using congrArg (fun f => (pullbackSymmetry X.hom (t.app i)).hom ≫ f) hei)
  refine ⟨i, ei', ?_⟩
  have hs := toLimit_square D t X.hom Z.hom c p hp i ⟨ei.hom, hei⟩
  rw [h] at hs
  have hs' := congrArg (fun f =>
    (pullbackSymmetry X.hom p).hom ≫ f ≫ (pullbackSymmetry (t.app i) Z.hom).hom) hs
  simpa [modelConeLeg, ei', es, Category.assoc] using hs'

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

private lemma curve_exists_modelIso
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (e : curvePlaceModelGenericFiber k F S X ≅ curvePlaceModelGenericFiber k F S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (ei : curvePlaceLevelModelBaseChange k F T.property X ≅
        curvePlaceLevelModelBaseChange k F T.property Z),
      curveGenericLeg k F S X T ≫ ei.hom.left =
        e.hom.left ≫ curveGenericLeg k F S Z T := by
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hc := spectrumConeIsLimit (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S)
  obtain ⟨i, ei, h⟩ := exists_modelIso (curveIntegerD k F S) (curveIntegerT k F S)
    (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S) X hc Z e
  exact ⟨i.unop, ei, h⟩

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

private lemma curve_spreadTopology_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ Y) :
    curvePlaceSpreadAdelePointTopology k F S X Y e =
      curvePlaceSpreadAdelePointTopology k F S Z Y f := by
  let eg := e ≪≫ f.symm
  obtain ⟨T, ei, hdesc⟩ := curve_exists_modelIso k F S X Z eg
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Z
  let := curvePlaceFixedModelAdelePointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  let := curvePlaceFixedModelAdelePointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property Z)
  let hX := equivHomeomorph (curvePlaceFixedModelInitialSetEquiv k F T.property X)
    (curvePlaceFixedModelInitialSetTopology k F S T.val T.property X)
  let hZ := equivHomeomorph (curvePlaceFixedModelInitialSetEquiv k F T.property Z)
    (curvePlaceFixedModelInitialSetTopology k F S T.val T.property Z)
  let h := hX.trans ((curvePlaceFixedModelIsoHomeomorph k F T.val ei).trans hZ.symm)
  have hstage (p : CurvePlaceFixedModelAdelePoints k F S X) :
      curvePlaceFixedModelInitialSetEquiv k F T.property Z (h p) =
        curvePlaceFixedModelInitialSetEquiv k F T.property X p ≫ ei.hom :=
    (curvePlaceFixedModelInitialSetEquiv k F T.property Z).apply_symm_apply _
  have hgeneric (p : CurvePlaceFixedModelAdelePoints k F S X) :
      curvePlaceGenericFiberAdelePointEquiv k F S Z (h p) =
        curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ eg.hom := by
    apply (curvePlaceGenericFiberAdelePointEquiv k F S Z).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [curvePlaceGenericFiberAdelePointEquiv_symm_left]
    change (h p).left = ((curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
      eg.hom.left) ≫ pullback.fst Z.hom (curveIntegerP k F S)
    calc
      _ = (curvePlaceFixedModelInitialSetEquiv k F T.property Z (h p)).left ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) :=
        (curvePlaceFixedModelInitialSetEquiv_left_fst k F T.property Z (h p)).symm
      _ = ((curvePlaceFixedModelInitialSetEquiv k F T.property X p).left ≫ ei.hom.left) ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) := by rw [hstage]; rfl
      _ = (((curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
          curveGenericLeg k F S X T) ≫ ei.hom.left) ≫
          pullback.fst Z.hom ((curveIntegerT k F S).app (op T)) := by
        rw [curve_genericLeg_point]
      _ = _ := by
        simp only [Category.assoc]
        rw [← Category.assoc (curveGenericLeg k F S X T), hdesc]
        simp only [Category.assoc, modelConeLeg_fst]
  apply transportedTopology_eq (curvePlaceSpreadAdelePointEquiv k F S X Y e)
    (curvePlaceSpreadAdelePointEquiv k F S Z Y f) h
  intro p
  change curvePlaceGenericFiberAdelePointEquiv k F S Z (h p) ≫ f.hom =
    curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ e.hom
  rw [hgeneric]
  simp [eg]

private def curveGenericFiberCompIso {U : Finset (AlgebraicCurve.Place k F)}
    (hSU : S ⊆ U) :
    curvePlaceModelGenericFiber k F U (curvePlaceLevelModelBaseChange k F hSU X) ≅
      curvePlaceModelGenericFiber k F S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype))
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))
    (by rw [← Spec.map_comp]; rfl) X

private lemma curve_spreadTopology_enlarge
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {U : Finset (AlgebraicCurve.Place k F)} (hSU : S ⊆ U)
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) :
    curvePlaceSpreadAdelePointTopology k F S X Y e =
      curvePlaceSpreadAdelePointTopology k F U (curvePlaceLevelModelBaseChange k F hSU X)
        Y (curveGenericFiberCompIso k F S X hSU ≪≫ e) := by
  let XU := curvePlaceLevelModelBaseChange k F hSU X
  let c := curveGenericFiberCompIso k F S X hSU
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F U XU
  let h := equivHomeomorph (curvePlaceFixedModelInitialSetEquiv k F hSU X)
    (curvePlaceFixedModelInitialSetTopology k F S U hSU X)
  have hgeneric (p : CurvePlaceFixedModelAdelePoints k F S X) :
      curvePlaceGenericFiberAdelePointEquiv k F U XU (h p) ≫ c.hom =
        curvePlaceGenericFiberAdelePointEquiv k F S X p := by
    apply (curvePlaceGenericFiberAdelePointEquiv k F S X).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [curvePlaceGenericFiberAdelePointEquiv_symm_left]
    change ((curvePlaceGenericFiberAdelePointEquiv k F U XU (h p)).left ≫
      c.hom.left) ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) = p.left
    have hc :
        c.hom.left ≫ pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) =
          pullback.fst XU.hom
              (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype)) ≫
            pullback.fst X.hom
              (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) :=
      modelPullbackCompIso_hom_left_fst _ _ _ _ X
    calc
      _ = (curvePlaceGenericFiberAdelePointEquiv k F U XU (h p)).left ≫
          (pullback.fst XU.hom
              (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype)) ≫
            pullback.fst X.hom
              (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU)))) := by
        rw [Category.assoc, hc]
      _ = ((curvePlaceGenericFiberAdelePointEquiv k F U XU (h p)).left ≫
          pullback.fst XU.hom
            (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F U).subtype))) ≫
          pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) :=
        (Category.assoc _ _ _).symm
      _ = (h p).left ≫ pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))) :=
        congrArg (fun q => q ≫ pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSU))))
          (curvePlaceGenericFiberAdelePointEquiv_left_fst k F U XU (h p))
      _ = _ := curvePlaceFixedModelInitialSetEquiv_left_fst k F hSU X p
  apply transportedTopology_eq (curvePlaceSpreadAdelePointEquiv k F S X Y e)
    (curvePlaceSpreadAdelePointEquiv k F U XU Y (c ≪≫ e)) h
  intro p
  change curvePlaceGenericFiberAdelePointEquiv k F U XU (h p) ≫ (c ≪≫ e).hom =
    curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ e.hom
  change (_ ≫ (c.hom ≫ e.hom)) = _
  rw [← Category.assoc, hgeneric]

end Curve

/-- Arbitrary function-field spreads induce literally equal adelic point topologies. -/
theorem curvePlaceSpreadTopologyIndependence :
    CurvePlaceSpreadTopologyIndependenceStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U X Z _ _ _ _ Y e f
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
  calc
    _ = curvePlaceSpreadAdelePointTopology k F V XV Y
        (curveGenericFiberCompIso k F S X hSV ≪≫ e) :=
      curve_spreadTopology_enlarge k F S X hSV Y e
    _ = curvePlaceSpreadAdelePointTopology k F V ZV Y
        (curveGenericFiberCompIso k F U Z hUV ≪≫ f) :=
      curve_spreadTopology_sameBase k F V XV ZV Y _ _
    _ = _ := (curve_spreadTopology_enlarge k F U Z hUV Y f).symm

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

private lemma number_exists_modelIso
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (e : numberFieldModelGenericFiber K S X ≅ numberFieldModelGenericFiber K S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (ei : numberFieldLevelModelBaseChange K T.property X ≅
        numberFieldLevelModelBaseChange K T.property Z),
      numberGenericLeg K S X T ≫ ei.hom.left =
        e.hom.left ≫ numberGenericLeg K S Z T := by
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hc := spectrumConeIsLimit ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S)
  obtain ⟨i, ei, h⟩ := exists_modelIso (numberIntegerD K S) (numberIntegerT K S)
    (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S) X hc Z e
  exact ⟨i.unop, ei, h⟩

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

private lemma number_spreadTopology_sameBase
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ Y) :
    numberFieldSpreadAdelePointTopology K S X Y e =
      numberFieldSpreadAdelePointTopology K S Z Y f := by
  let eg := e ≪≫ f.symm
  obtain ⟨T, ei, hdesc⟩ := number_exists_modelIso K S X Z eg
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Z
  let := numberFieldFixedModelAdelePointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  let := numberFieldFixedModelAdelePointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property Z)
  let hX := equivHomeomorph (numberFieldFixedModelInitialSetEquiv K T.property X)
    (numberFieldFixedModelInitialSetTopology K S T.val T.property X)
  let hZ := equivHomeomorph (numberFieldFixedModelInitialSetEquiv K T.property Z)
    (numberFieldFixedModelInitialSetTopology K S T.val T.property Z)
  let h := hX.trans ((numberFieldFixedModelIsoHomeomorph K T.val ei).trans hZ.symm)
  have hstage (p : NumberFieldFixedModelAdelePoints K S X) :
      numberFieldFixedModelInitialSetEquiv K T.property Z (h p) =
        numberFieldFixedModelInitialSetEquiv K T.property X p ≫ ei.hom :=
    (numberFieldFixedModelInitialSetEquiv K T.property Z).apply_symm_apply _
  have hgeneric (p : NumberFieldFixedModelAdelePoints K S X) :
      numberFieldGenericFiberAdelePointEquiv K S Z (h p) =
        numberFieldGenericFiberAdelePointEquiv K S X p ≫ eg.hom := by
    apply (numberFieldGenericFiberAdelePointEquiv K S Z).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [numberFieldGenericFiberAdelePointEquiv_symm_left]
    change (h p).left = ((numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
      eg.hom.left) ≫ pullback.fst Z.hom (numberIntegerP K S)
    calc
      _ = (numberFieldFixedModelInitialSetEquiv K T.property Z (h p)).left ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) :=
        (numberFieldFixedModelInitialSetEquiv_left_fst K T.property Z (h p)).symm
      _ = ((numberFieldFixedModelInitialSetEquiv K T.property X p).left ≫ ei.hom.left) ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) := by rw [hstage]; rfl
      _ = (((numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
          numberGenericLeg K S X T) ≫ ei.hom.left) ≫
          pullback.fst Z.hom ((numberIntegerT K S).app (op T)) := by
        rw [number_genericLeg_point]
      _ = _ := by
        simp only [Category.assoc]
        rw [← Category.assoc (numberGenericLeg K S X T), hdesc]
        simp only [Category.assoc, modelConeLeg_fst]
  apply transportedTopology_eq (numberFieldSpreadAdelePointEquiv K S X Y e)
    (numberFieldSpreadAdelePointEquiv K S Z Y f) h
  intro p
  change numberFieldGenericFiberAdelePointEquiv K S Z (h p) ≫ f.hom =
    numberFieldGenericFiberAdelePointEquiv K S X p ≫ e.hom
  rw [hgeneric]
  simp [eg]

private def numberGenericFiberCompIso {U : Finset (FinitePlace K)}
    (hSU : S ⊆ U) :
    numberFieldModelGenericFiber K U (numberFieldLevelModelBaseChange K hSU X) ≅
      numberFieldModelGenericFiber K S X :=
  modelPullbackCompIso
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))
    (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype))
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))
    (by rw [← Spec.map_comp]; rfl) X

private lemma number_spreadTopology_enlarge
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    {U : Finset (FinitePlace K)} (hSU : S ⊆ U)
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) :
    numberFieldSpreadAdelePointTopology K S X Y e =
      numberFieldSpreadAdelePointTopology K U (numberFieldLevelModelBaseChange K hSU X)
        Y (numberGenericFiberCompIso K S X hSU ≪≫ e) := by
  let XU := numberFieldLevelModelBaseChange K hSU X
  let c := numberGenericFiberCompIso K S X hSU
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K U XU
  let h := equivHomeomorph (numberFieldFixedModelInitialSetEquiv K hSU X)
    (numberFieldFixedModelInitialSetTopology K S U hSU X)
  have hgeneric (p : NumberFieldFixedModelAdelePoints K S X) :
      numberFieldGenericFiberAdelePointEquiv K U XU (h p) ≫ c.hom =
        numberFieldGenericFiberAdelePointEquiv K S X p := by
    apply (numberFieldGenericFiberAdelePointEquiv K S X).symm.injective
    rw [Equiv.symm_apply_apply]
    apply RingPoint.ext
    rw [numberFieldGenericFiberAdelePointEquiv_symm_left]
    change ((numberFieldGenericFiberAdelePointEquiv K U XU (h p)).left ≫
      c.hom.left) ≫
        pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) = p.left
    have hc :
        c.hom.left ≫ pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) =
          pullback.fst XU.hom
              (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype)) ≫
            pullback.fst X.hom
              (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) :=
      modelPullbackCompIso_hom_left_fst _ _ _ _ X
    calc
      _ = (numberFieldGenericFiberAdelePointEquiv K U XU (h p)).left ≫
          (pullback.fst XU.hom
              (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype)) ≫
            pullback.fst X.hom
              (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU)))) := by
        rw [Category.assoc, hc]
      _ = ((numberFieldGenericFiberAdelePointEquiv K U XU (h p)).left ≫
          pullback.fst XU.hom
            (Spec.map (CommRingCat.ofHom ((U : Set (FinitePlace K)).integer K).toSubring.subtype))) ≫
          pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) :=
        (Category.assoc _ _ _).symm
      _ = (h p).left ≫ pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))) :=
        congrArg (fun q => q ≫ pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSU))))
          (numberFieldGenericFiberAdelePointEquiv_left_fst K U XU (h p))
      _ = _ := numberFieldFixedModelInitialSetEquiv_left_fst K hSU X p
  apply transportedTopology_eq (numberFieldSpreadAdelePointEquiv K S X Y e)
    (numberFieldSpreadAdelePointEquiv K U XU Y (c ≪≫ e)) h
  intro p
  change numberFieldGenericFiberAdelePointEquiv K U XU (h p) ≫ (c ≪≫ e).hom =
    numberFieldGenericFiberAdelePointEquiv K S X p ≫ e.hom
  change (_ ≫ (c.hom ≫ e.hom)) = _
  rw [← Category.assoc, hgeneric]

end NumberField

/-- Arbitrary number-field spreads induce literally equal adelic point topologies. -/
theorem numberFieldSpreadTopologyIndependence :
    NumberFieldSpreadTopologyIndependenceStatement.{u} := by
  intro K _ _ S U X Z _ _ _ _ Y e f
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
  calc
    _ = numberFieldSpreadAdelePointTopology K V XV Y
        (numberGenericFiberCompIso K S X hSV ≪≫ e) :=
      number_spreadTopology_enlarge K S X hSV Y e
    _ = numberFieldSpreadAdelePointTopology K V ZV Y
        (numberGenericFiberCompIso K U Z hUV ≪≫ f) :=
      number_spreadTopology_sameBase K V XV ZV Y _ _
    _ = _ := (number_spreadTopology_enlarge K U Z hUV Y f).symm

/-- The adelic topology is independent of every finite-type arithmetic spread. -/
theorem adelicSpreadTopologyIndependence : AdelicSpreadTopologyIndependenceStatement.{u} :=
  ⟨curvePlaceSpreadTopologyIndependence, numberFieldSpreadTopologyIndependence⟩

end Langlands.Global
