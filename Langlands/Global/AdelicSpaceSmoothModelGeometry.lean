import Langlands.Global.AdelicSpaceProperModelReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothChartLimitDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitConnectedFibresDescent

/-! # Smooth models with nonempty geometrically connected fibres -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.SchemeLimitModel
open Langlands.Global.AdelicSpaceProperModelReduction

namespace Langlands.Global.AdelicSpaceSmoothModelGeometry

/-- Smoothness and nonempty geometric connectedness hold at one common incoming stage. -/
theorem smoothConnectedDescent :
    SpaceLimitPropertyDescends.{u}
      (fun f => IsSmoothMorphism f ∧ HasGeometricallyConnectedFibres f) := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs hY f
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have hs := spaceLimitSmoothDescent I D c hc i X Y hXqs hX hYqs hY f
  have hg := spaceLimitGeometricallyConnectedFibresDescent
    I D c hc i X Y hXqs hX hYqs hY f
  constructor
  · rintro ⟨hsm, hgc⟩
    obtain ⟨j, r, hj⟩ := hs.mp hsm
    let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
    have hgc' : HasGeometricallyConnectedFibres
        (baseChangeMap (c.π.app j) (baseChangeMap (D.map r) f)) :=
      HasGeometricallyConnectedFibres.of_arrow_iso (e.app X).symm (e.app Y).symm
        (e.inv.naturality f).symm hgc
    have hg' := spaceLimitGeometricallyConnectedFibresDescent I D c hc j
      (baseChange (D.map r) X) (baseChange (D.map r) Y)
      (hXqs.baseChange (g := D.map r)) (hX.baseChange (g := D.map r))
      (hYqs.baseChange (g := D.map r)) (hY.baseChange (g := D.map r))
      (baseChangeMap (D.map r) f)
    obtain ⟨k, s, hk⟩ := hg'.mp hgc'
    let e' := baseChangeCompNatIso (D.map r) (D.map s) (D.map (s ≫ r))
      (D.map_comp s r).symm
    exact ⟨k, s ≫ r,
      IsSmoothMorphism.of_arrow_iso (e'.app X) (e'.app Y)
        (e'.hom.naturality f).symm (hj.baseChangeMap (g := D.map s)),
      HasGeometricallyConnectedFibres.of_arrow_iso (e'.app X) (e'.app Y)
        (e'.hom.naturality f).symm hk⟩
  · rintro ⟨j, r, hsm, hgc⟩
    exact ⟨hs.mpr ⟨j, r, hsm⟩, hg.mpr ⟨j, r, hgc⟩⟩

/-- An actual smooth arrow with nonempty geometrically connected fibres between
identified limit fibres has a model with both properties at one affine stage. -/
theorem exists_smoothConnected_model
    (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (B : Scheme.{u}) [IsAffine B] (t : D ⟶ (Functor.const I).obj B)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ B)
    (hcompat : ∀ i, c.π.app i ≫ t.app i = p)
    (X Z : AlgebraicSpace B) (hX : IsSeparated X)
    (hfpX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hZ : IsSeparated Z)
    (hfpZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z)
    (Y W : AlgebraicSpace c.pt) (e : baseChange p X ≅ Y) (f : baseChange p Z ≅ W)
    (g : Y ⟶ W) (hg : IsSmoothMorphism g) (hgc : HasGeometricallyConnectedFibres g) :
    ∃ (j : I) (M N : AlgebraicSpace (D.obj j)),
      IsSeparated M ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) M ∧
      IsSeparated N ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) N ∧
      ∃ (eT : baseChange (c.π.app j) M ≅ Y)
        (fT : baseChange (c.π.app j) N ≅ W) (gm : M ⟶ N),
        IsSmoothMorphism gm ∧ HasGeometricallyConnectedFibres gm ∧
          baseChangeMap (c.π.app j) gm ≫ fT.hom = eT.hom ≫ g := by
  let φ := e.hom ≫ g ≫ f.inv
  obtain ⟨i, φi, hi⟩ := spaceLimitMorphismDescent I D B t c hc p hcompat X Z hX
    (hfpX.mono (fun _ _ _ h => h.2)) (hfpZ.mono (fun _ _ _ h => h.1)) φ
  let eiX := BaseChangeComparison.compIso (t.app i) (c.π.app i) p (hcompat i) X
  let eiZ := BaseChangeComparison.compIso (t.app i) (c.π.app i) p (hcompat i) Z
  have wi := compIso_hom_comp_eq _ _ _ (hcompat i) φ φi hi
  have wi' : (eiX ≪≫ e).hom ≫ g =
      baseChangeMap (c.π.app i) φi ≫ (eiZ ≪≫ f).hom := by
    simpa [φ, eiX, eiZ, Category.assoc] using congrArg (fun a => a ≫ f.hom) wi
  have wrev : (eiX ≪≫ e).inv ≫ baseChangeMap (c.π.app i) φi =
      g ≫ (eiZ ≪≫ f).inv := by
    apply (cancel_mono (eiZ ≪≫ f).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← wi', Iso.inv_hom_id_assoc]
  have hφi := And.intro
    (IsSmoothMorphism.of_arrow_iso (eiX ≪≫ e).symm (eiZ ≪≫ f).symm wrev hg)
    (HasGeometricallyConnectedFibres.of_arrow_iso
      (eiX ≪≫ e).symm (eiZ ≪≫ f).symm wrev hgc)
  obtain ⟨j, r, hj⟩ := (smoothConnectedDescent I D c hc i (baseChange (t.app i) X)
    (baseChange (t.app i) Z) (quasiSeparated_of_separated hX.baseChange)
    hfpX.baseChange (quasiSeparated_of_separated hZ.baseChange) hfpZ.baseChange φi).mp hφi
  let M := baseChange (D.map r) (baseChange (t.app i) X)
  let N := baseChange (D.map r) (baseChange (t.app i) Z)
  let ejX := BaseChangeComparison.compIso (D.map r) (c.π.app j) (c.π.app i)
    (c.w r) (baseChange (t.app i) X)
  let ejZ := BaseChangeComparison.compIso (D.map r) (c.π.app j) (c.π.app i)
    (c.w r) (baseChange (t.app i) Z)
  refine ⟨j, M, N, hX.baseChange.baseChange, hfpX.baseChange.baseChange,
    hZ.baseChange.baseChange, hfpZ.baseChange.baseChange,
    ejX ≪≫ eiX ≪≫ e, ejZ ≪≫ eiZ ≪≫ f, baseChangeMap (D.map r) φi, hj.1, hj.2, ?_⟩
  have wj := (baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i)
    (c.w r)).hom.naturality φi
  change baseChangeMap (c.π.app j) (baseChangeMap (D.map r) φi) ≫ ejZ.hom =
    ejX.hom ≫ baseChangeMap (c.π.app i) φi at wj
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [wj]
  simpa only [Iso.trans_hom, Category.assoc] using
    congrArg (fun a => ejX.hom ≫ a) wi'.symm

/-- Actual stage models of a smooth map with nonempty geometrically connected fibres. -/
structure SmoothConnectedStageModel {I : Type u} [SmallCategory I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {Y W : AlgebraicSpace c.pt} (g : Y ⟶ W) where
  stage : I
  source : AlgebraicSpace (D.obj stage)
  target : AlgebraicSpace (D.obj stage)
  source_separated : IsSeparated source
  source_atlas : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) source
  target_separated : IsSeparated target
  target_atlas : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) target
  source_iso : baseChange (c.π.app stage) source ≅ Y
  target_iso : baseChange (c.π.app stage) target ≅ W
  map : source ⟶ target
  map_smooth : IsSmoothMorphism map
  map_connected : HasGeometricallyConnectedFibres map
  commutes : baseChangeMap (c.π.app stage) map ≫ target_iso.hom = source_iso.hom ≫ g

/-- Choose a stage model using only the published unconditional descent theorems. -/
def smoothConnectedStageModel
    (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (B : Scheme.{u}) [IsAffine B] (t : D ⟶ (Functor.const I).obj B)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ B)
    (hcompat : ∀ i, c.π.app i ≫ t.app i = p)
    (X Z : AlgebraicSpace B) (hX : IsSeparated X)
    (hfpX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hZ : IsSeparated Z)
    (hfpZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z)
    (Y W : AlgebraicSpace c.pt) (e : baseChange p X ≅ Y) (f : baseChange p Z ≅ W)
    (g : Y ⟶ W) (hg : IsSmoothMorphism g) (hgc : HasGeometricallyConnectedFibres g) :
    SmoothConnectedStageModel D c g :=
  Classical.choice (by
    obtain ⟨j, M, N, hM, hfpM, hN, hfpN, eT, fT, gm, hgm, hgcM, w⟩ :=
      exists_smoothConnected_model I D B t c hc p hcompat X Z hX hfpX hZ hfpZ Y W e f g hg hgc
    exact ⟨⟨j, M, N, hM, hfpM, hN, hfpN, eT, fT, gm, hgm, hgcM, w⟩⟩)

/-- The smooth connected-fibre model over a common ring of integers, for the
actual generic arrow between arbitrary supplied separated finite-type models. -/
theorem curvePlaceSpaceSmoothConnectedModel :
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F)), S.Nonempty → U.Nonempty →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      IsSeparated Z → FiniteTypeOverRing (curvePlaceSIntegers k F U) Z →
      ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of F)))
        (_e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
        (_f : curvePlaceSpaceGenericFiber k F U Z ≅ W) (g : Y ⟶ W),
        IsSmoothMorphism g → HasGeometricallyConnectedFibres g →
          ∃ (T : Finset (AlgebraicCurve.Place k F))
            (M N : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T)))),
            T.Nonempty ∧ IsSeparated M ∧ FiniteTypeOverRing (curvePlaceSIntegers k F T) M ∧
            IsSeparated N ∧ FiniteTypeOverRing (curvePlaceSIntegers k F T) N ∧
            ∃ (eT : curvePlaceSpaceGenericFiber k F T M ≅ Y)
              (fT : curvePlaceSpaceGenericFiber k F T N ≅ W) (gm : M ⟶ N),
              IsSmoothMorphism gm ∧ HasGeometricallyConnectedFibres gm ∧
                baseChangeMap (Spec.map (CommRingCat.ofHom
                  (curvePlaceSIntegers k F T).subtype)) gm ≫ fT.hom = eT.hom ≫ g := by
  intro k F _ _ _ _ _ _ _ S U hS _ X Z hX hftX hZ hftZ Y W e f g hg hgc
  classical
  let V := S ∪ U
  have hSV : S ⊆ V := Finset.subset_union_left
  have hUV : U ⊆ V := Finset.subset_union_right
  let qX := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSV))
  let qZ := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hUV))
  let XV := baseChange qX X
  let ZV := baseChange qZ Z
  let eV : curvePlaceSpaceGenericFiber k F V XV ≅ Y :=
    BaseChangeComparison.compIso qX _ _ (by rw [← Spec.map_comp]; rfl) X ≪≫ e
  let fV : curvePlaceSpaceGenericFiber k F V ZV ≅ W :=
    BaseChangeComparison.compIso qZ _ _ (by rw [← Spec.map_comp]; rfl) Z ≪≫ f
  let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  let : IsNoetherianRing (curvePlaceSIntegers k F U) :=
    (adelicSIntegersNoetherian.1 k F U).1
  have hfpX := (finitePresentationAtlas hftX).baseChange (g := qX)
  have hfpZ := (finitePresentationAtlas hftZ).baseChange (g := qZ)
  let model := smoothConnectedStageModel _
      (spectrumDiagram _ (curvePlaceSIntegersOverDiagram k F V)) _
      (spectrumStructure _ (curvePlaceSIntegersOverDiagram k F V))
      (spectrumCone _ _ (curvePlaceSIntegersOverCocone k F V))
      (spectrumConeIsLimit _ _ _ (curvePlaceSIntegersOverIsColimit k F V))
      (spectrumBaseMap _ _ (curvePlaceSIntegersOverCocone k F V))
      (spectrumCone_compat _ _ _) XV ZV hX.baseChange hfpX hZ.baseChange hfpZ
      Y W eV fV g hg hgc
  exact ⟨model.stage.unop.val, model.source, model.target,
    hS.mono (hSV.trans model.stage.unop.property), model.source_separated,
    finiteType_of_finitePresentationAtlas model.source_atlas, model.target_separated,
    finiteType_of_finitePresentationAtlas model.target_atlas, model.source_iso,
    model.target_iso, model.map, model.map_smooth, model.map_connected, model.commutes⟩

/-- The smooth connected-fibre model over a common ring of integers, for the
actual generic arrow between arbitrary supplied separated finite-type models. -/
theorem numberFieldSpaceSmoothConnectedModel :
  ∀ (K : Type u) [Field K] [NumberField K] (S U : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    IsSeparated Z → FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z →
    ∀ (Y W : AlgebraicSpace (Spec (CommRingCat.of K)))
      (_e : numberFieldSpaceGenericFiber K S X ≅ Y)
      (_f : numberFieldSpaceGenericFiber K U Z ≅ W) (g : Y ⟶ W),
      IsSmoothMorphism g → HasGeometricallyConnectedFibres g →
        ∃ (T : Finset (FinitePlace K))
          (M N : AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K)))),
          IsSeparated M ∧ FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) M ∧
          IsSeparated N ∧ FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) N ∧
          ∃ (eT : numberFieldSpaceGenericFiber K T M ≅ Y)
            (fT : numberFieldSpaceGenericFiber K T N ≅ W) (gm : M ⟶ N),
            IsSmoothMorphism gm ∧ HasGeometricallyConnectedFibres gm ∧
              baseChangeMap (Spec.map (CommRingCat.ofHom
                ((T : Set (FinitePlace K)).integer K).toSubring.subtype)) gm ≫ fT.hom =
                  eT.hom ≫ g := by
  intro K _ _ S U X Z hX hftX hZ hftZ Y W e f g hg hgc
  classical
  let V := S ∪ U
  have hSV : S ⊆ V := Finset.subset_union_left
  have hUV : U ⊆ V := Finset.subset_union_right
  let qX := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSV))
  let qZ := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hUV))
  let XV := baseChange qX X
  let ZV := baseChange qZ Z
  let eV : numberFieldSpaceGenericFiber K V XV ≅ Y :=
    BaseChangeComparison.compIso qX _ _ (by rw [← Spec.map_comp]; rfl) X ≪≫ e
  let fV : numberFieldSpaceGenericFiber K V ZV ≅ W :=
    BaseChangeComparison.compIso qZ _ _ (by rw [← Spec.map_comp]; rfl) Z ≪≫ f
  let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  let : IsNoetherianRing ((U : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K U).1
  have hfpX := (finitePresentationAtlas hftX).baseChange (g := qX)
  have hfpZ := (finitePresentationAtlas hftZ).baseChange (g := qZ)
  let model := smoothConnectedStageModel _
      (spectrumDiagram _ (numberFieldSIntegersOverDiagram K V)) _
      (spectrumStructure _ (numberFieldSIntegersOverDiagram K V))
      (spectrumCone _ _ (numberFieldSIntegersOverCocone K V))
      (spectrumConeIsLimit _ _ _ (numberFieldSIntegersOverIsColimit K V))
      (spectrumBaseMap _ _ (numberFieldSIntegersOverCocone K V))
      (spectrumCone_compat _ _ _) XV ZV hX.baseChange hfpX hZ.baseChange hfpZ
      Y W eV fV g hg hgc
  exact ⟨model.stage.unop.val, model.source, model.target, model.source_separated,
    finiteType_of_finitePresentationAtlas model.source_atlas, model.target_separated,
    finiteType_of_finitePresentationAtlas model.target_atlas, model.source_iso,
    model.target_iso, model.map, model.map_smooth, model.map_connected, model.commutes⟩

end Langlands.Global.AdelicSpaceSmoothModelGeometry
