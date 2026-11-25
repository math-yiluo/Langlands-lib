/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # RingedToposAdaptedFlatResolution

Source: Stacks Project, Tag 0G7E (lemma-pullback-K-flat), adapted resolution step.
(auxiliary; not a blueprint node). -/

@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
namespace SheafOfModules

section PullbackHelpers

open CategoryTheory.Functor MonoidalCategory

private def sheafUliftIso_adapted
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (A : Type uD) [Category.{vD} A] (U : A ⥤ Type w)
    [J.HasSheafCompose U] [J.HasSheafCompose (U ⋙ uliftFunctor.{w, w})] :
    sheafCompose J (U ⋙ uliftFunctor.{w, w}) ≅ sheafCompose J U :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ uliftTrivial (U.obj (M.obj.obj X)))
      (by intros; rfl))) (by intros; rfl)

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def inverseImageOfUniverses_adapted (I : AlgebraicInverseImage L R RI) :
    AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R RI := by
  let eR := sheafUliftIso_adapted JC CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eS := sheafUliftIso_adapted JD CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eM := isoWhiskerLeft (toSheaf ((sheafCompose JC
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) <|
    sheafUliftIso_adapted JC AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let eN := isoWhiskerLeft (toSheaf ((sheafCompose JD
    (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) <|
    sheafUliftIso_adapted JD AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let er := L.mapIso (eR.app R) ≪≫ I.ringUnderlying ≪≫ (eS.app RI).symm
  let em := isoWhiskerLeft I.modules eN ≪≫ I.moduleUnderlying ≪≫
    isoWhiskerRight eM.symm L
  refine
    { ringUnderlying := er
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      modules := I.modules
      moduleUnderlying := em
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app R).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [er, em, eS, eN, sheafUliftIso_adapted, uliftTrivial, Functor.map_comp] using hr

end PullbackHelpers

section ResolutionHelpers

universe u v r
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

open CategoryTheory.Functor MonoidalCategory
open scoped ZeroObject

set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{r} O

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory

private theorem tensorPreadditive_adapted : MonoidalPreadditive A := by
  have (M : A) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

-- This is the free-presheaf cover used in KFlatResolutionIndependentCoefficients.
-- Its construction needs colimit preservation of tensor, rather than a chosen internal Hom.
private noncomputable def tensorSheafificationIso_adapted
    (F : PresheafOfModules.{r} (O).obj) :
    tensorRight ((PresheafOfModules.sheafification.{r} (𝟙 (O).obj)).obj F) ≅
      (SheafOfModules.forget.{r} O ⋙
        PresheafOfModules.restrictScalars (𝟙 (O).obj)) ⋙ tensorRight F ⋙
        PresheafOfModules.sheafification.{r} (𝟙 (O).obj) := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight a F)

private theorem hasFunctorialFlatResolution_adapted : Abelian.HasFunctorialFlatResolution A := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{r} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{r} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{r} (O).obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free ((O).obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{r} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  have hT (M : A) : ObjectProperty.flat (T.obj M) := by
    have hflat : PreservesFiniteLimits (tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro D
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have := hflat
    have : PreservesLimitsOfSize.{0, 0} V :=
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_adapted R (G.obj (V.obj M))).symm
    have : PreservesFiniteLimits (tensorLeft (T.obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M)).symm
    have (X : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) := by
      have := tensorLeft_preservesColimits_independentCoefficients R X
      exact preservesColimitsOfSize_shrink (tensorLeft X)
    have : PreservesFiniteColimits (tensorRight (T.obj M)) :=
      preservesFiniteColimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M))
    exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩
  exact ⟨{ F := ObjectProperty.lift _ T hT
           π := π
           epi_π_app M := by
             have := hτ (V.obj M)
             dsimp [π]
             infer_instance }⟩

private theorem hasExactColimits_int_adapted : HasExactColimitsOfShape ℤ A := by
  have := AB5OfSize_of_univLE.{0, 0, r, r} AddCommGrpCat.{r}
  exact HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf.{r} O)

attribute [local instance] tensorPreadditive_adapted

private theorem tensorLeftColimits_adapted (M : A) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  have := tensorLeft_preservesColimits_independentCoefficients R M
  exact preservesColimitsOfSize_shrink (tensorLeft M)

private theorem tensorRightColimits_adapted (M : A) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  have := tensorLeftColimits_adapted R M
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

attribute [local instance] tensorLeftColimits_adapted tensorRightColimits_adapted
  hasExactColimits_int_adapted

private theorem flatOnSite_of_categorical_adapted (M : A) (hM : ObjectProperty.flat M) :
    IsFlatOnSite (J := J) (R := R) M := by
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm hM.2

private theorem categorical_of_flatOnSite_adapted (M : A)
    (hM : IsFlatOnSite (J := J) (R := R) M) : ObjectProperty.flat M := by
  have hr : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) hM
  exact ⟨(exactFunctor _ _).prop_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight M).symm hr, hr⟩

private theorem all_tensorLeftColimits_adapted :
    ∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  tensorLeftColimits_adapted R

private theorem all_tensorRightColimits_adapted :
    ∀ M : A, PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  tensorRightColimits_adapted R

attribute [local instance] all_tensorLeftColimits_adapted all_tensorRightColimits_adapted

private theorem hasTensor_adapted :
    ∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂ := by
  have (K : Type r) : HasColimitsOfShape (Discrete K) (PresheafOfModules.{r} (O).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  infer_instance

private theorem hasGoodTensor₁₂_adapted :
    ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance

private theorem hasGoodTensor₂₃_adapted :
    ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance

private theorem hasTensor₄_adapted :
    ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance

attribute [local instance] hasTensor_adapted hasGoodTensor₁₂_adapted
  hasGoodTensor₂₃_adapted hasTensor₄_adapted

private theorem independent_of_categorical_adapted (K : CochainComplex A ℤ)
    (hK : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat K) :
    K.IsKFlatIndependentCoefficients := by
  intro Z hZ
  let T := tensorRight K
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hK.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

end ResolutionHelpers

/-- A flat K-flat resolution may be chosen with K-flat termwise pullback.
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, first paragraph of the proof
of lemma-pullback-K-flat, using Tags 077J, 06YQ and 06YR.
(auxiliary; not a blueprint node).

Proof: choose a strictly compatible tower E_n of bounded-above flat resolutions of
P.truncLE n. Each augmentation is a quasi-isomorphism. Take its degreewise filtered
colimit L, with the induced augmentation q to P. Exact filtered colimits commute
with homology, while the good truncations stabilize in each fixed degree. Hence q
is a quasi-isomorphism. Flat sheaves and K-flat complexes are closed under filtered
colimits; bounded-above flat complexes are K-flat. Thus L has flat terms and is
K-flat. The filtered-colimit preservation theorem for the specified module pullback makes
uStar preserve the displayed degreewise colimit. Each uStar(E_n) is still bounded above
and has flat terms by flat pullback, hence is K-flat. Their filtered colimit uStar(L)
is K-flat. This construction makes no K-flatness or flat-term assumption on P. -/
theorem exists_pullback_adapted_flat_resolution
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    ∃ (L : CochainComplex (SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) (q : L ⟶ P),
      L.IsKFlatIndependentCoefficients ∧
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (L.X n)) ∧ QuasiIso q ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  classical
  let A := SheafOfModules.{w} ((sheafCompose JC
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let B := SheafOfModules.{w} ((sheafCompose JD
    (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
  have (K : Type w) : HasColimitsOfShape (Discrete K) (PresheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (K : Type w) : HasColimitsOfShape (Discrete K) (PresheafOfModules.{w}
      ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (K : Type w) : HasColimitsOfShape (Discrete K) A :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive_adapted R
  have := hasTensor_adapted R
  have := hasGoodTensor₁₂_adapted R
  have := hasGoodTensor₂₃_adapted R
  have := hasTensor₄_adapted R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) :=
    tensorLeftColimits_adapted R M
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    tensorRightColimits_adapted R M
  have (M : A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).obj M) := inferInstance
  have (M : A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).flip.obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ A := hasExactColimits_int_adapted R
  have := hasFunctorialFlatResolution_adapted R
  have : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat :=
    ObjectProperty.flat.essImage_ι_le
  let L := Λ.resolutionFunctor.obj P
  let q : L ⟶ P := Λ.resolutionNatTrans.app P
  have hq : QuasiIso q := inferInstance
  let presentation := Λ.colimitOfShapeFlatResolutionFunctorObj hι P
  have hL : L.IsKFlatIndependentCoefficients := by
    apply independent_of_categorical_adapted R
    exact Λ.kFlat_resolutionFunctor_obj hι P
  have hLflat (n : ℤ) : IsFlatOnSite (J := JC) (R := R) (L.X n) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
    apply flatOnSite_of_categorical_adapted R
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n) presentation.isColimit)
      (fun j ↦ (presentation.prop_diag_obj j).1 n)
  refine ⟨L, q, hL, hLflat, hq, ?_⟩
  -- Enlarge the countable diagram into the coefficient universe and transport back.
  have : PreservesColimitsOfShape (ULiftHom.{w} (ULift.{w} ℤ)) uStar :=
    preservesFilteredColimits_ringedToposPullback uInv uPush adj I c uStar hobj hmap _
  have : PreservesColimitsOfShape ℤ uStar :=
    preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv ℤ).symm uStar
  let F := uStar.mapHomologicalComplex (.up ℤ)
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory S
  let := symmetricCategory S
  let := tensorPreadditive_adapted S
  have := hasTensor_adapted S
  have := hasGoodTensor₁₂_adapted S
  have := hasGoodTensor₂₃_adapted S
  have := hasTensor₄_adapted S
  have (M : B) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) :=
    tensorLeftColimits_adapted S M
  have (M : B) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    tensorRightColimits_adapted S M
  have (M : B) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor B).obj M) := inferInstance
  have (M : B) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor B).flip.obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ B := hasExactColimits_int_adapted S
  apply independent_of_categorical_adapted S
  apply ObjectProperty.prop_of_isColimit _ (isColimitOfPreserves F presentation.isColimit)
  intro j
  obtain ⟨b, hb⟩ := (presentation.prop_diag_obj j).2
  have := hb
  have : CochainComplex.IsStrictlyLE ((presentation.diag ⋙ F).obj j) b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact uStar.map_isZero ((presentation.diag.obj j).isZero_of_isStrictlyLE b i hi)
  apply CochainComplex.kFlat_of_isStrictlyLE_of_flat _ b
  intro n
  apply categorical_of_flatOnSite_adapted S
  change IsFlatOnSite (uStar.obj ((presentation.diag.obj j).X n))
  rw [hobj]
  exact isFlat_ringedToposPullback.{uC, vC, uD, vD, w, w} uInv uPush adj
    (inverseImageOfUniverses_adapted I) c _
    (flatOnSite_of_categorical_adapted R _ ((presentation.prop_diag_obj j).1 n))

end SheafOfModules
