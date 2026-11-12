import Langlands.Global.AdelicSpaceProperInputsStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePointsIsoTransport

/-! # Proper models from morphism descent and properness descent -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.SchemeLimitModel

namespace Langlands.Global.AdelicSpaceProperModelReduction

/-- Separated algebraic spaces are quasi-separated. -/
theorem quasiSeparated_of_separated {B : Scheme.{u}} {X : AlgebraicSpace B}
    (hX : IsSeparated X) : IsQuasiSeparated X := by
  refine MorphismProperty.relative_monotone ?_ _ hX
  intro A C f hf
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.forget B).map f) := hf
  exact (inferInstance : QuasiCompact ((Over.forget B).map f))

/-- Properness transports through an isomorphism of arrows. -/
theorem proper_of_arrow_iso {B : Scheme.{u}} {X Z X' Z' : AlgebraicSpace B}
    {f : X ⟶ Z} {f' : X' ⟶ Z'} (eX : X ≅ X') (eZ : Z ≅ Z')
    (w : eX.hom ≫ f' = f ≫ eZ.hom) (hf : IsProperMorphism f) :
    IsProperMorphism f' := by
  refine ⟨?_, IsQuasiCompactMorphism.of_arrow_iso eX eZ w hf.2.1,
    IsLocallyOfFiniteTypeMorphism.of_arrow_iso eX eZ w hf.2.2.1,
    IsUniversallyClosedMorphism.of_arrow_iso eX eZ w hf.2.2.2⟩
  apply (MorphismProperty.arrow_mk_iso_iff
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget B)).relative (schemeYoneda B)).diagonal
    (Arrow.isoMk ((forgetToPresheaf B).mapIso eX)
      ((forgetToPresheaf B).mapIso eZ) ((forgetToPresheaf B).congr_map w))).mp
  exact hf.1

section Comparisons

variable {B C E : Scheme.{u}} (q : C ⟶ B) (r : E ⟶ C) (p : E ⟶ B)
    (h : r ≫ q = p)

/-- Convert the section equality in morphism descent to a commuting arrow square.
Adapted from Worker 208's shared arithmetic independence draft. -/
theorem compIso_hom_comp_eq {X Z : AlgebraicSpace B}
    (φ : baseChange p X ⟶ baseChange p Z) (φi : baseChange q X ⟶ baseChange q Z)
    (hφ : ∀ (W : Over E) (x : (baseChange p X).sections W),
      mapSections φ W x =
        Z.pullback
          (Over.homMk (𝟙 W.left) (by simp [← h]) :
            (Over.map p).obj W ⟶ (Over.map q).obj ((Over.map r).obj W))
          (mapSections φi ((Over.map r).obj W)
            (X.pullback
              (Over.homMk (𝟙 W.left) (by simp [← h]) :
                (Over.map q).obj ((Over.map r).obj W) ⟶ (Over.map p).obj W) x))) :
    (BaseChangeComparison.compIso q r p h X).hom ≫ φ =
      baseChangeMap r φi ≫ (BaseChangeComparison.compIso q r p h Z).hom := by
  apply (homEquiv _ _).injective
  ext W y
  change mapSections φ W.unop
      (mapSections (BaseChangeComparison.compIso q r p h X).hom W.unop y) =
    mapSections (BaseChangeComparison.compIso q r p h Z).hom W.unop
      (mapSections φi ((Over.map r).obj W.unop) y)
  rw [BaseChangeComparison.mapSections_compIso_hom,
    BaseChangeComparison.mapSections_compIso_hom, hφ, ← pullback_comp]
  rw [BaseChangeComparison.pullback_congr_left X (g := 𝟙 _) (by simp), pullback_id]
  exact BaseChangeComparison.pullback_congr_left Z rfl _

end Comparisons

/-- A proper morphism at a stage together with its identified limit fibres,
separated models, finite-presentation atlases, and the exact generic square. -/
structure ProperStageModel {I : Type u} [SmallCategory I]
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
  map_proper : IsProperMorphism map
  commutes : baseChangeMap (c.π.app stage) map ≫ target_iso.hom = source_iso.hom ≫ g

/-- Given morphism descent and properness descent, a proper arrow between the
identified limit fibres has a proper model at a stage. -/
theorem exists_proper_model
    (hm : SpaceLimitMorphismDescent.{u})
    (hp : SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f))
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
    (g : Y ⟶ W) (hg : IsProperMorphism g) :
    ∃ (j : I) (M N : AlgebraicSpace (D.obj j)),
      IsSeparated M ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) M ∧
      IsSeparated N ∧
      HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) N ∧
      ∃ (eT : baseChange (c.π.app j) M ≅ Y)
        (fT : baseChange (c.π.app j) N ≅ W) (gm : M ⟶ N),
        IsProperMorphism gm ∧ baseChangeMap (c.π.app j) gm ≫ fT.hom = eT.hom ≫ g := by
  let φ := e.hom ≫ g ≫ f.inv
  obtain ⟨i, φi, hi⟩ := hm I D B t c hc p hcompat X Z hX
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
  have hφi := proper_of_arrow_iso (eiX ≪≫ e).symm (eiZ ≪≫ f).symm wrev hg
  obtain ⟨j, r, hj⟩ := (hp I D c hc i (baseChange (t.app i) X)
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
    ejX ≪≫ eiX ≪≫ e, ejZ ≪≫ eiZ ≪≫ f, baseChangeMap (D.map r) φi, hj, ?_⟩
  have wj := (baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i)
    (c.w r)).hom.naturality φi
  change baseChangeMap (c.π.app j) (baseChangeMap (D.map r) φi) ≫ ejZ.hom =
    ejX.hom ≫ baseChangeMap (c.π.app i) φi at wj
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [wj]
  simpa only [Iso.trans_hom, Category.assoc] using
    congrArg (fun a => ejX.hom ≫ a) wi'.symm

/-- Choose actual proper stage-model data from morphism and properness descent.
The two geometric descent statements remain explicit inputs. -/
def properStageModelOfDescent
    (hm : SpaceLimitMorphismDescent.{u})
    (hp : SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f))
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
    (g : Y ⟶ W) (hg : IsProperMorphism g) : ProperStageModel D c g :=
  Classical.choice (by
    obtain ⟨j, M, N, hM, hfpM, hN, hfpN, eT, fT, gm, hgm, w⟩ :=
      exists_proper_model hm hp I D B t c hc p hcompat X Z hX hfpX hZ hfpZ Y W e f g hg
    exact ⟨⟨j, M, N, hM, hfpM, hN, hfpN, eT, fT, gm, hgm, w⟩⟩)

/-- Over a Noetherian ring a finite-type atlas is a finite-presentation atlas,
with its original quasi-compactness condition. -/
theorem finitePresentationAtlas {C : Type u} [CommRing C] [IsNoetherianRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} (h : FiniteTypeOverRing C X) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X := by
  obtain ⟨U, a, ha, hs, hl, hq⟩ := h
  exact ⟨U, a, ha, hs, LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 hl, hq⟩

/-- A locally finitely presented quasi-compact atlas is a finite-type atlas. -/
theorem finiteType_of_finitePresentationAtlas {C : Type u} [CommRing C]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    (h : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    FiniteTypeOverRing C X := by
  apply h.mono
  intro A B f hf
  have := hf.1
  exact ⟨inferInstance, hf.2⟩

/-- The function-field proper-model conclusion, conditional on the two descent inputs. -/
theorem curvePlaceSpaceProperModel_of_descent
    (hm : SpaceLimitMorphismDescent.{u})
    (hp : SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f)) :
    CurvePlaceSpaceProperModelStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U hS _ X Z hX hftX hZ hftZ Y W e f g hg
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
  let model := properStageModelOfDescent hm hp _
      (spectrumDiagram _ (curvePlaceSIntegersOverDiagram k F V)) _
      (spectrumStructure _ (curvePlaceSIntegersOverDiagram k F V))
      (spectrumCone _ _ (curvePlaceSIntegersOverCocone k F V))
      (spectrumConeIsLimit _ _ _ (curvePlaceSIntegersOverIsColimit k F V))
      (spectrumBaseMap _ _ (curvePlaceSIntegersOverCocone k F V))
      (spectrumCone_compat _ _ _) XV ZV hX.baseChange hfpX hZ.baseChange hfpZ
      Y W eV fV g hg
  exact ⟨model.stage.unop.val, model.source, model.target,
    hS.mono (hSV.trans model.stage.unop.property), model.source_separated,
    finiteType_of_finitePresentationAtlas model.source_atlas, model.target_separated,
    finiteType_of_finitePresentationAtlas model.target_atlas, model.source_iso,
    model.target_iso, model.map, model.map_proper, model.commutes⟩

/-- The number-field proper-model conclusion, allowing empty initial sets,
conditional on the two descent inputs. -/
theorem numberFieldSpaceProperModel_of_descent
    (hm : SpaceLimitMorphismDescent.{u})
    (hp : SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f)) :
    NumberFieldSpaceProperModelStatement.{u} := by
  intro K _ _ S U X Z hX hftX hZ hftZ Y W e f g hg
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
  let model := properStageModelOfDescent hm hp _
      (spectrumDiagram _ (numberFieldSIntegersOverDiagram K V)) _
      (spectrumStructure _ (numberFieldSIntegersOverDiagram K V))
      (spectrumCone _ _ (numberFieldSIntegersOverCocone K V))
      (spectrumConeIsLimit _ _ _ (numberFieldSIntegersOverIsColimit K V))
      (spectrumBaseMap _ _ (numberFieldSIntegersOverCocone K V))
      (spectrumCone_compat _ _ _) XV ZV hX.baseChange hfpX hZ.baseChange hfpZ
      Y W eV fV g hg
  exact ⟨model.stage.unop.val, model.source, model.target, model.source_separated,
    finiteType_of_finitePresentationAtlas model.source_atlas, model.target_separated,
    finiteType_of_finitePresentationAtlas model.target_atlas, model.source_iso,
    model.target_iso, model.map, model.map_proper, model.commutes⟩

/-- The full proper arithmetic model replacement follows from morphism descent
and the properness case of property descent, in the same arbitrary universe. -/
theorem adelicSpaceProperModel_of_descent
    (hm : SpaceLimitMorphismDescent.{u})
    (hp : SpaceLimitPropertyDescends.{u} (fun f => IsProperMorphism f)) :
    AdelicSpaceProperModelStatement.{u} :=
  ⟨curvePlaceSpaceProperModel_of_descent hm hp,
    numberFieldSpaceProperModel_of_descent hm hp⟩

end Langlands.Global.AdelicSpaceProperModelReduction
