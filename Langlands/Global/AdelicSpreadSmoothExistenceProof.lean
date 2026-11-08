import Langlands.Global.AdelicSpreadModelMorphisms
import Langlands.Global.AdelicSpreadSmoothExistenceStatement
import Langlands.Global.AdelicSpreadSeparatedExistenceProof
import Langlands.Global.AdelicSpreadEventualSmoothFiberGeometryProof
import Langlands.Global.AdelicFixedModelTransition
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Langlands.AlgebraicGeometry.SchemeLimitModelProof

/-! # Compatible smooth morphisms over actual arithmetic integer rings -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology.SpreadModelMorphisms

namespace Langlands.AlgebraicGeometry.PointTopology

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
private lemma modelConeLeg_property (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (i : I)
    (f : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Z)
    (hf : P f.left)
    (fi : (Over.pullback (t.app i)).obj X ⟶ (Over.pullback (t.app i)).obj Z)
    (h : modelConeLeg D t c p hp X i ≫ fi.left =
      f.left ≫ modelConeLeg D t c p hp Z i) :
    P ((Over.pullback (c.π.app i)).map fi).left := by
  have hn := modelConeLeg_naturality D t c p hp X Z i f fi h
  have heq : (Over.pullback (c.π.app i)).map fi =
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) X).hom ≫ f ≫
        (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) Z).inv := by
    apply (cancel_mono
      (modelPullbackCompIso (t.app i) (c.π.app i) p (hp i) Z).hom).mp
    simpa using hn
  rw [heq, Over.comp_left, Over.comp_left]
  simpa only [MorphismProperty.cancel_left_of_respectsIso,
    MorphismProperty.cancel_right_of_respectsIso] using hf

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

private lemma curve_spread_property_sameBase
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hdescent : CurvePlaceSpreadEventualPropertyStatement.{u} P)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ W)
    (g : Y ⟶ W) (hg : P g.left) :
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F T.val)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (eU : curvePlaceModelGenericFiber k F T.val M ≅ Y)
        (fU : curvePlaceModelGenericFiber k F T.val N ≅ W) (gm : M ⟶ N),
        P gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            (curvePlaceSIntegers k F T.val).subtype))).map gm ≫ fU.hom = eU.hom ≫ g := by
  let eg := e.hom ≫ g ≫ f.inv
  have heg : P eg.left := by
    simpa only [eg, Over.comp_left, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso] using hg
  obtain ⟨T, fi, hdesc⟩ := curve_exists_modelMorphism k F S X Z eg
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let ZT := curvePlaceLevelModelBaseChange k F T.property Z
  let pT := Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F T.val).subtype)
  let egT : curvePlaceModelGenericFiber k F T.val XT ⟶
      curvePlaceModelGenericFiber k F T.val ZT := (Over.pullback pT).map fi
  have hgT : P egT.left :=
    modelConeLeg_property (curveIntegerD k F S) (curveIntegerT k F S)
      (curveIntegerC k F S) (curveIntegerP k F S) (curveIntegerW k F S)
      X Z P (op T) eg heg fi hdesc
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
  obtain ⟨U, hU⟩ := (hdescent k F T.val XT ZT fi).mp hgT
  let a := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F U.property))
  let XU := curvePlaceLevelModelBaseChange k F U.property XT
  let ZU := curvePlaceLevelModelBaseChange k F U.property ZT
  let fiU : XU ⟶ ZU := (Over.pullback a).map fi
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
  let : IsSeparated ZU.hom := by
    dsimp [ZU, ZT, curvePlaceLevelModelBaseChange]
    infer_instance
  have hsep : IsSeparated XU.hom := by
    dsimp [XU, XT, curvePlaceLevelModelBaseChange]
    infer_instance
  exact ⟨⟨U.val, T.property.trans U.property⟩, XU, ZU,
    inferInstance, inferInstance, hsep, inferInstance, inferInstance,
    inferInstance, eU, fU, fiU, hU, hm⟩

end Curve

/-- Compatible models follow from separated model existence, morphism
descent, and eventual detection of an isomorphism-invariant property. -/
theorem curvePlaceSpreadMorphismPropertyExistence
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hdescent : CurvePlaceSpreadEventualPropertyStatement.{u} P) :
    CurvePlaceSpreadMorphismPropertyExistenceStatement.{u} P := by
  intro k F _ _ _ _ _ _ _ S Y W _ _ _ _ _ _ g hg
  obtain ⟨T, N, hNft, hNqc, hNsep, ⟨f⟩⟩ := curvePlaceSpreadSeparatedExistence k F S W
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  obtain ⟨U, M, hMft, hMqc, hMsep, ⟨e⟩⟩ := curvePlaceSpreadSeparatedExistence k F T.val Y
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let NU := curvePlaceLevelModelBaseChange k F U.property N
  let : LocallyOfFiniteType NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let : IsSeparated NU.hom := by
    dsimp [NU, curvePlaceLevelModelBaseChange]
    infer_instance
  let fU := curveGenericFiberCompIso k F T.val N U.property ≪≫ f
  obtain ⟨V, M', N', hMft', hMqc', hMsep', hNft', hNqc', hNsep', e', f', gm, hgm, hm⟩ :=
    curve_spread_property_sameBase k F U.val M NU P hdescent Y W e fU g hg
  exact ⟨⟨V.val, T.property.trans (U.property.trans V.property)⟩, M', N',
    hMft', hMqc', hMsep', hNft', hNqc', hNsep', e', f', gm, hgm, hm⟩

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

private lemma number_spread_property_sameBase
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hdescent : NumberFieldSpreadEventualPropertyStatement.{u} P)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ W)
    (g : Y ⟶ W) (hg : P g.left) :
    ∃ (T : AdelicLevelIndexAbove S)
      (M N : Over (Spec (CommRingCat.of ((T.val : Set (FinitePlace K)).integer K)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧ IsSeparated M.hom ∧
      LocallyOfFiniteType N.hom ∧ QuasiCompact N.hom ∧ IsSeparated N.hom ∧
      ∃ (eU : numberFieldModelGenericFiber K T.val M ≅ Y)
        (fU : numberFieldModelGenericFiber K T.val N ≅ W) (gm : M ⟶ N),
        P gm.left ∧
          (Over.pullback (Spec.map (CommRingCat.ofHom
            ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype))).map gm ≫ fU.hom = eU.hom ≫ g := by
  let eg := e.hom ≫ g ≫ f.inv
  have heg : P eg.left := by
    simpa only [eg, Over.comp_left, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso] using hg
  obtain ⟨T, fi, hdesc⟩ := number_exists_modelMorphism K S X Z eg
  let XT := numberFieldLevelModelBaseChange K T.property X
  let ZT := numberFieldLevelModelBaseChange K T.property Z
  let pT := Spec.map (CommRingCat.ofHom ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype)
  let egT : numberFieldModelGenericFiber K T.val XT ⟶
      numberFieldModelGenericFiber K T.val ZT := (Over.pullback pT).map fi
  have hgT : P egT.left :=
    modelConeLeg_property (numberIntegerD K S) (numberIntegerT K S)
      (numberIntegerC K S) (numberIntegerP K S) (numberIntegerW K S)
      X Z P (op T) eg heg fi hdesc
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
  obtain ⟨U, hU⟩ := (hdescent K T.val XT ZT fi).mp hgT
  let a := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K U.property))
  let XU := numberFieldLevelModelBaseChange K U.property XT
  let ZU := numberFieldLevelModelBaseChange K U.property ZT
  let fiU : XU ⟶ ZU := (Over.pullback a).map fi
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
  let : IsSeparated ZU.hom := by
    dsimp [ZU, ZT, numberFieldLevelModelBaseChange]
    infer_instance
  have hsep : IsSeparated XU.hom := by
    dsimp [XU, XT, numberFieldLevelModelBaseChange]
    infer_instance
  exact ⟨⟨U.val, T.property.trans U.property⟩, XU, ZU,
    inferInstance, inferInstance, hsep, inferInstance, inferInstance,
    inferInstance, eU, fU, fiU, hU, hm⟩

end NumberField

/-- The same compatible-model construction for the original number field. -/
theorem numberFieldSpreadMorphismPropertyExistence
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hdescent : NumberFieldSpreadEventualPropertyStatement.{u} P) :
    NumberFieldSpreadMorphismPropertyExistenceStatement.{u} P := by
  intro K _ _ S Y W _ _ _ _ _ _ g hg
  obtain ⟨T, N, hNft, hNqc, hNsep, ⟨f⟩⟩ := numberFieldSpreadSeparatedExistence K S W
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  obtain ⟨U, M, hMft, hMqc, hMsep, ⟨e⟩⟩ := numberFieldSpreadSeparatedExistence K T.val Y
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let NU := numberFieldLevelModelBaseChange K U.property N
  let : LocallyOfFiniteType NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let : IsSeparated NU.hom := by
    dsimp [NU, numberFieldLevelModelBaseChange]
    infer_instance
  let fU := numberGenericFiberCompIso K T.val N U.property ≪≫ f
  obtain ⟨V, M', N', hMft', hMqc', hMsep', hNft', hNqc', hNsep', e', f', gm, hgm, hm⟩ :=
    number_spread_property_sameBase K U.val M NU P hdescent Y W e fU g hg
  exact ⟨⟨V.val, T.property.trans (U.property.trans V.property)⟩, M', N',
    hMft', hMqc', hMsep', hNft', hNqc', hNsep', e', f', gm, hgm, hm⟩

/-- Actual compatible smooth function-field models, with optional fixed
nonempty geometrically connected pure-dimensional fibres. -/
theorem curvePlaceSpreadSmoothExistence : CurvePlaceSpreadSmoothExistenceStatement.{u} :=
  ⟨curvePlaceSpreadMorphismPropertyExistence @Smooth
      curvePlaceSpreadEventualSmoothFiberGeometry.1,
    fun d => curvePlaceSpreadMorphismPropertyExistence _
      (curvePlaceSpreadEventualSmoothFiberGeometry.2 d).2⟩

/-- The same two compatible-model conclusions over the original number field. -/
theorem numberFieldSpreadSmoothExistence : NumberFieldSpreadSmoothExistenceStatement.{u} :=
  ⟨numberFieldSpreadMorphismPropertyExistence @Smooth
      numberFieldSpreadEventualSmoothFiberGeometry.1,
    fun d => numberFieldSpreadMorphismPropertyExistence _
      (numberFieldSpreadEventualSmoothFiberGeometry.2 d).2⟩

/-- Both arithmetic smooth-model existence clauses. -/
theorem adelicSpreadSmoothExistence : AdelicSpreadSmoothExistenceStatement.{u} :=
  ⟨curvePlaceSpreadSmoothExistence, numberFieldSpreadSmoothExistence⟩

end Langlands.Global
