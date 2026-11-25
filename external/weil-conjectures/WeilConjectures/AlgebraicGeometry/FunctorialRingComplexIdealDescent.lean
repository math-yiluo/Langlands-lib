/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
public import WeilConjectures.CategoryTheory.AugmentedComplexGluing
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.AlgebraicGeometry.RingFamilyLocallyEqualModels
import WeilConjectures.AlgebraicGeometry.RingFamilyRestriction

/-! # Descent from locally equal section ideals

Source: Stacks Project, algebraization.tex, Tag 099E, second and third paragraphs.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

attribute [local irreducible] PresheafOfModules.sheafification
attribute [local irreducible] SheafOfModules.instAbelian
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

private def ringTarget
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) : ringedSiteComplex O := ringedSiteRingComplex O

private instance commRingForgetHasSheafCompose
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

private theorem commRingToTypeCompose
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget CommRingCat.{u}) := inferInstance

private theorem addCommGrpToTypeCompose
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance

private theorem abelianHasSheafify
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} := inferInstance

private theorem abelianLocalEquivalences
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance 100000] commRingForgetHasSheafCompose commRingToTypeCompose
  addCommGrpToTypeCompose abelianHasSheafify abelianLocalEquivalences

private abbrev modulePreadditive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Preadditive (SheafOfModules.{u} R) :=
  SheafOfModules.instPreadditive R

private abbrev presheafModulePreadditive
    {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    Preadditive (PresheafOfModules.{u} R) := PresheafOfModules.instPreadditive

private abbrev moduleAddCommGroup
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) : AddCommGroup M :=
  M.isAddCommGroup

private abbrev moduleModule
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) : Module R M := M.isModule

private abbrev moduleHomCoe
    {R : Type u} [Ring R] {M N : ModuleCat.{u} R} :
    CoeFun (ModuleCat.Hom M N) (fun _ ↦ M → N) := ⟨fun g ↦ g.hom⟩

attribute [local instance] modulePreadditive presheafModulePreadditive
  moduleAddCommGroup moduleModule moduleHomCoe

private instance moduleZeroObject
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : HasZeroObject (SheafOfModules.{u} R) := inferInstance

private abbrev moduleZeroMorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : HasZeroMorphisms (SheafOfModules.{u} R) :=
  Preadditive.preadditiveHasZeroMorphisms

attribute [local instance] moduleZeroMorphisms

private instance standardOverMap_preservesZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (SheafOfModules.overMap.{u} R a).PreservesZeroMorphisms :=
  ⟨by intro M N; ext X x; rfl⟩

private def directOverMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (R.over W) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ (Over.map a) (R.over U).obj).obj M.val
      isSheaf := ((SheafOfModules.overMap R a).obj M).isSheaf }
  map g :=
    { val := (PresheafOfModules.pushforward₀ (Over.map a) (R.over U).obj).map g.val }

private def directOverMapUnitIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (directOverMap R a).obj (SheafOfModules.unit (R.over U)) ≅
      SheafOfModules.unit (R.over W) := Iso.refl _

private def sheafIsoOfComponents
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (M N : SheafOfModules.{u} R)
    (e : ∀ X, M.val.obj X ≅ N.val.obj X)
    (h : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y),
      M.val.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (e Y).hom =
        (e X).hom ≫ N.val.map f) : M ≅ N :=
  { hom := ⟨(PresheafOfModules.isoMk e h).hom⟩
    inv := ⟨(PresheafOfModules.isoMk e h).inv⟩
    hom_inv_id := by ext1; exact (PresheafOfModules.isoMk e h).hom_inv_id
    inv_hom_id := by ext1; exact (PresheafOfModules.isoMk e h).inv_hom_id }

private def directOverMapIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    directOverMap R a ≅ SheafOfModules.overMap R a :=
  NatIso.ofComponents
    (fun M ↦ sheafIsoOfComponents (R.over W) _ _ (fun X ↦ Iso.refl _)
      (by intro X Y f; ext x; rfl))
    (by intro M N g; ext X x; rfl)

private theorem directOverMapIso_inv_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (X : (Over W)ᵒᵖ)
    (x : M.val.obj ((Over.map a).op.obj X)) :
    ((directOverMapIso R a).inv.app M).val.app X x = x := by
  rfl

private instance overMap_preservesZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (directOverMap R a).PreservesZeroMorphisms :=
  ⟨by intro M N; ext X x; rfl⟩

private theorem directOverMapComplexIso_inv_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ) (n : ℤ) (X : (Over W)ᵒᵖ)
    (x : (M.X n).val.obj ((Over.map a).op.obj X)) :
    ((((NatIso.mapHomologicalComplex (directOverMapIso R a) (.up ℤ)).app M).inv.f n).val.app
      X x) = x := by
  exact directOverMapIso_inv_apply R a (M.X n) X x

private instance overFunctor_preservesZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    (SheafOfModules.overFunctor.{u} R U).PreservesZeroMorphisms :=
  ⟨by intro M N; ext X x; rfl⟩

private def unitToSheaf
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (M : PresheafOfModules.{u} R.obj) :
    M ⟶ (SheafOfModules.forget R).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj M) := by
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M

private def modelUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) (r : ℕ)
    (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
    (ringFamilyPresheafComplex O K ε m hm r f).X n ⟶
      ((ringFamilySheafModel O K ε m hm r f).1.X n).val :=
  unitToSheaf _ ((ringFamilyPresheafComplex O K ε m hm r f).X n)

private instance overMap_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (directOverMap.{u} R a).Additive :=
  ⟨fun {_ _} b c ↦ by ext X x; rfl⟩

private abbrev commonSpanSections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U W : C) (a : W ⟶ U)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    Fin r → ((O.over W).obj ⋙ forget CommRingCat).sections :=
  ringFamilyRestrictedSections (J := J.over W) (L := J.over U)
    (Over.map a) (O.over U) r (fun i ↦ ringedSliceSection O U (f i))

private def familyComponent
    (K : RingComplexFamily.{u}) (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG})
    (n : ℤ) : ModuleCat.{u} A :=
  ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)

private def familyTransport
    (K : RingComplexFamily.{u}) (A : CommRingCat.{u}) (I I' : {I : Ideal A // I.FG})
    (h : I = I') (n : ℤ) (x : familyComponent K A I n) : familyComponent K A I' n :=
  ((eqToIso (congrArg (fun L ↦ familyComponent K A L n) h)).toLinearEquiv).toFun x

private theorem standard_restricted_ringFamily_model_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    ∃ e : (ringFamilySheafModel (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).1 ≅
      ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (e.hom.f n).val.app X
          ((modelUnit (O.over W) K ε m hm r
            (commonSpanSections O U W a r f) n).app X x) =
          ((modelUnit (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i)) n).app ((Over.map a).op.obj X) x) := by
  exact exists_ringFamilySheafModel_restrictionIso
    (J := J.over W) (L := J.over U) (Over.map a) (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))

private theorem restricted_ringFamily_model_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    ∃ e : (ringFamilySheafModel (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).1 ≅
      ((directOverMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (e.hom.f n).val.app X
          ((modelUnit (O.over W) K ε m hm r
            (commonSpanSections O U W a r f) n).app X x) =
          ((modelUnit (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i)) n).app ((Over.map a).op.obj X) x) := by
  obtain ⟨e, he⟩ := standard_restricted_ringFamily_model_iso O K ε m hm U W a r f
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ :=
    (ringFamilySheafModel (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).1
  let d := (NatIso.mapHomologicalComplex (directOverMapIso R a) (.up ℤ)).app M
  refine ⟨e ≪≫ d.symm, ?_⟩
  intro n X x
  change (d.inv.f n).val.app X
    ((e.hom.f n).val.app X ((modelUnit (O.over W) K ε m hm r
      (commonSpanSections O U W a r f) n).app X x)) = _
  have hh := congrArg ((d.inv.f n).val.app X) (he n X x)
  exact hh.trans (directOverMapComplexIso_inv_apply R a M n X _)

private def sliceModelComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) ℤ :=
  (ringFamilySheafModel (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i))).1

private def ringZeroProjection
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    (ringTarget O).X 0 ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom

private def restrictedRingZeroProjection
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C) :
    ((((SheafOfModules.overFunctor
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
        (.up ℤ)).obj (ringTarget O)).X 0) ⟶
      (SheafOfModules.overFunctor
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.overFunctor
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).map (ringZeroProjection O)

private def ringRestrictionInv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C) :
    ringTarget (O.over U) ⟶
      ((SheafOfModules.overFunctor
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
          (.up ℤ)).obj (ringTarget O) :=
  (ringedRestrictionRingComplexIso O U).inv

private def sliceAugmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) (U : C)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    sliceModelComplex O K ε m hm U r f ⟶
      ((SheafOfModules.overFunctor
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
          (.up ℤ)).obj (ringTarget O) :=
  (ringFamilySheafModel (O.over U) K ε m hm r
    (fun t ↦ ringedSliceSection O U (f t))).2 ≫ ringRestrictionInv O U

private def sliceUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) (n : ℤ) :
    (ringFamilyPresheafComplex (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).X n ⟶
        ((sliceModelComplex O K ε m hm U r f).X n).val :=
  modelUnit (O.over U) K ε m hm r (fun i ↦ ringedSliceSection O U (f i)) n

private def restrictedModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W)) ℤ :=
  ((directOverMap
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
      (.up ℤ)).obj (sliceModelComplex O K ε m hm U r f)

private def commonSpanCanonical
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g) : Prop :=
  ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
    (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
      ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
    (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).X n).obj X),
    (q.hom.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
      (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
        (familyTransport K ((O.over W).obj.obj X) _ _ h n x)

private theorem commonSpanEqualityCover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y) := by
  intro X
  obtain ⟨S, hS, hs⟩ := heq X.left X.hom
  refine ⟨(Sieve.overEquiv X).symm S, J.overEquiv_symm_mem_over X S hS, ?_⟩
  intro Y k hk
  apply Subtype.ext
  change Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ a).op (f t))) =
    Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ b).op (g t)))
  have hh := hs Y.left k.left hk
  simpa only [← Category.assoc, Over.w k] using hh

private theorem commonSpanModels_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∃ q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g,
      commonSpanCanonical O K ε m hm U V W a b r s f g q := by
  have hlocal : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y)).val =
          (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)).val := by
    intro X
    obtain ⟨S, hS, hs⟩ := heq X.left X.hom
    refine ⟨(Sieve.overEquiv X).symm S, J.overEquiv_symm_mem_over X S hS, ?_⟩
    intro Y k hk
    change Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ a).op (f t))) =
      Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ b).op (g t)))
    have hh := hs Y.left k.left hk
    simpa only [← Category.assoc, Over.w k] using hh
  obtain ⟨z, _, hz⟩ := ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit
    (O.over W) K ε m hm r (commonSpanSections O U W a r f)
      s (commonSpanSections O V W b s g) hlocal
  obtain ⟨ea, ha⟩ := restricted_ringFamily_model_iso O K ε m hm U W a r f
  obtain ⟨eb, hb⟩ := restricted_ringFamily_model_iso O K ε m hm V W b s g
  refine ⟨ea.symm ≪≫ z ≪≫ eb, ?_⟩
  intro n X h x
  let η := (modelUnit (O.over W) K ε m hm r
    (commonSpanSections O U W a r f) n).app X x
  have hc := congrArg (fun t ↦ (t.f n).val.app X η) ea.hom_inv_id
  change (ea.inv.f n).val.app X ((ea.hom.f n).val.app X η) = η at hc
  have ha' := (congrArg ((ea.inv.f n).val.app X) (ha n X x).symm).trans hc
  change (eb.hom.f n).val.app X
    ((z.hom.f n).val.app X ((ea.inv.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x))) = _
  exact (congrArg (fun t ↦ (eb.hom.f n).val.app X ((z.hom.f n).val.app X t)) ha').trans
    ((congrArg ((eb.hom.f n).val.app X) (hz n X h x)).trans
      (hb n X (familyTransport K ((O.over W).obj.obj X) _ _ h n x)))

private abbrev sliceValue
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C}
    (M : SheafOfModules.{u} (R.over U)) (a : W ⟶ U) : ModuleCat.{u} (R.obj.obj (op W)) :=
  M.val.obj (op (Over.mk a))

private def spanEvaluationEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) :
    (sliceValue R ((directOverMap R a).obj M) (𝟙 W)) ≃ₗ[
        R.obj.obj (op W)]
      (sliceValue R M a) :=
  (eqToIso (congrArg (fun b : W ⟶ U ↦
    (sliceValue R M b))
      (Category.id_comp a))).toLinearEquiv

private theorem spanEvaluationEquiv_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M N : SheafOfModules.{u} (R.over U)) (g : M ⟶ N)
    (x : ((directOverMap R a).obj M).val.obj (op (Over.mk (𝟙 W)))) :
    spanEvaluationEquiv R a N
        ((((directOverMap R a).map g).val.app (op (Over.mk (𝟙 W)))) x) =
      g.val.app (op (Over.mk a)) (spanEvaluationEquiv R a M x) := by
  have h := eqToHom_naturality
    (C := ModuleCat (R.obj.obj (op W)))
    (f := fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk b))))
    (g := fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from N.val.obj (op (Over.mk b))))
    (fun b : W ⟶ U ↦ (show M.val.obj (op (Over.mk b)) ⟶ N.val.obj (op (Over.mk b)) from
      g.val.app (op (Over.mk b)))) (Category.id_comp a)
  exact congrArg (fun z ↦ z x) h

private def spanTransitionEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N) (n : ℤ) :
    (show ModuleCat (R.obj.obj (op W)) from (M.X n).val.obj (op (Over.mk a))) ≃ₗ[
      R.obj.obj (op W)]
      (show ModuleCat (R.obj.obj (op W)) from (N.X n).val.obj (op (Over.mk b))) :=
  let e : (show ModuleCat (R.obj.obj (op W)) from
      ((directOverMap R a).obj (M.X n)).val.obj (op (Over.mk (𝟙 W)))) ≃ₗ[
        R.obj.obj (op W)] (show ModuleCat (R.obj.obj (op W)) from
      ((directOverMap R b).obj (N.X n)).val.obj (op (Over.mk (𝟙 W)))) :=
    ((SheafOfModules.evaluation (R.over W) (op (Over.mk (𝟙 W)))).mapIso
      (HomologicalComplex.Hom.isoApp q n)).toLinearEquiv
  (spanEvaluationEquiv R a (M.X n)).symm.trans
    (e.trans (spanEvaluationEquiv R b (N.X n)))

private theorem spanTransitionEquiv_differential
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (n k : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a b M N q k ((M.d n k).val.app (op (Over.mk a)) x) =
      (N.d n k).val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q n x) := by
  let y : ((directOverMap R a).obj (M.X n)).val.obj
      (op (Over.mk (𝟙 W))) := (spanEvaluationEquiv R a (M.X n)).symm x
  have ha := spanEvaluationEquiv_naturality R a (M.X n) (M.X k) (M.d n k) y
  have hb := spanEvaluationEquiv_naturality R b (N.X n) (N.X k) (N.d n k)
    ((q.hom.f n).val.app (op (Over.mk (𝟙 W))) y)
  have hd := congrArg (fun z ↦ z.val.app (op (Over.mk (𝟙 W))) y) (q.hom.comm n k)
  have hi : (spanEvaluationEquiv R a (M.X k)).symm
      ((M.d n k).val.app (op (Over.mk a)) x) =
      (((directOverMap R a).map (M.d n k)).val.app (op (Over.mk (𝟙 W)))) y := by
    exact (spanEvaluationEquiv R a (M.X k)).injective
      (by simpa only [y, LinearEquiv.apply_symm_apply] using ha.symm)
  change spanEvaluationEquiv R b (N.X k)
    ((q.hom.f k).val.app (op (Over.mk (𝟙 W)))
      ((spanEvaluationEquiv R a (M.X k)).symm
        ((M.d n k).val.app (op (Over.mk a)) x))) = _
  rw [hi]
  exact (congrArg (spanEvaluationEquiv R b (N.X k)) hd.symm).trans hb

private theorem spanTransitionEquiv_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V T W : C}
    (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (R.over T)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (z : ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N ≅
      ((directOverMap R c).mapHomologicalComplex (.up ℤ)).obj P)
    (n : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a c M P (q ≪≫ z) n x =
      spanTransitionEquiv R b c N P z n (spanTransitionEquiv R a b M N q n x) := by
  simp only [spanTransitionEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

private def glueDataOfComparisons
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {A : Type u} (U : A → C)
    (B : CochainComplex (SheafOfModules.{u} R) ℤ)
    (L : ∀ i, CochainComplex (SheafOfModules.{u} (R.over (U i))) ℤ)
    (α : ∀ i, L i ⟶ ((SheafOfModules.overFunctor R (U i)).mapHomologicalComplex
      (.up ℤ)).obj B)
    (q : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj (L i) ≅
        ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj (L j))
    (hqc : ∀ (i j k : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) (c : W ⟶ U k),
      (q i k W a c).hom = (q i j W a b).hom ≫ (q j k W b c).hom)
    (hn : ∀ (n : ℤ) (i j : A) (W V : C) (k : V ⟶ W)
      (a : W ⟶ U i) (b : W ⟶ U j) (x : ((L i).X n).val.obj (op (Over.mk a))),
      spanTransitionEquiv R (k ≫ a) (k ≫ b) (L i) (L j)
        (q i j V (k ≫ a) (k ≫ b)) n
          (((L i).X n).val.map
            (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
        ((L j).X n).val.map
          (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
            (spanTransitionEquiv R a b (L i) (L j) (q i j W a b) n x))
    (hα : ∀ (n : ℤ) (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j)
      (x : ((L i).X n).val.obj (op (Over.mk a))),
      ((α j).f n).val.app (op (Over.mk b))
        (spanTransitionEquiv R a b (L i) (L j) (q i j W a b) n x) =
          ((α i).f n).val.app (op (Over.mk a)) x) :
    SheafOfModules.AugmentedComplexGlueData R U B L α where
  transition n i j W a b := spanTransitionEquiv R a b (L i) (L j) (q i j W a b) n
  naturality := hn
  cocycle := by
    intro n i j k W a b c x
    have hi : q i k W a c = q i j W a b ≪≫ q j k W b c :=
      Iso.ext (hqc i j k W a b c)
    change spanTransitionEquiv R a c (L i) (L k) (q i k W a c) n x = _
    rw [hi]
    exact spanTransitionEquiv_comp R a b c (L i) (L j) (L k)
      (q i j W a b) (q j k W b c) n x
  differential := by
    intro n k i j W a b x
    exact spanTransitionEquiv_differential R a b (L i) (L j) (q i j W a b) n k x
  augmentation := hα

attribute [local irreducible] glueDataOfComparisons

private theorem direct_sheafification_hom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : PresheafOfModules.{u} (R.over U).obj) (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (N : SheafOfModules.{u} (R.over W))
    (τ χ : (directOverMap R a).obj
      ((PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj M) ⟶ N)
    (h : ∀ (X : (Over W)ᵒᵖ), E X → ∀ x : M.obj ((Over.map a).op.obj X),
      τ.val.app X ((unitToSheaf (R.over U) M).app ((Over.map a).op.obj X) x) =
        χ.val.app X ((unitToSheaf (R.over U) M).app ((Over.map a).op.obj X) x)) :
    τ = χ := by
  let S := (PresheafOfModules.sheafification (𝟙 (R.over U).obj)).obj M
  let d := (directOverMapIso R a).app S
  have hh : d.inv ≫ τ = d.inv ≫ χ := by
    apply PresheafOfModules.restricted_sheafification_hom_ext
      (J := J.over W) (K := J.over U) (Over.map a) (R.over U) M E hcover
    intro X hX x
    change τ.val.app X (d.inv.val.app X
      ((unitToSheaf (R.over U) M).app ((Over.map a).op.obj X) x)) =
        χ.val.app X (d.inv.val.app X
          ((unitToSheaf (R.over U) M).app ((Over.map a).op.obj X) x))
    have ht := directOverMapIso_inv_apply R a S X
      ((unitToSheaf (R.over U) M).app ((Over.map a).op.obj X) x)
    exact (congrArg (τ.val.app X) ht).trans
      ((h X hX x).trans (congrArg (χ.val.app X) ht).symm)
  exact (cancel_epi d.inv).1 hh

private theorem commonSpanHom_ext_degree
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) (U W : C) (a : W ⟶ U)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) (n : ℤ)
    (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (B : SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W))
    (τ χ : (restrictedModel O K ε m hm U W a r f).X n ⟶ B)
    (h : ∀ (X : (Over W)ᵒᵖ), E X →
      ∀ x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n).obj ((Over.map a).op.obj X),
      τ.val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        χ.val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x)) :
    τ = χ := by
  exact direct_sheafification_hom_ext
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a
    ((ringFamilyPresheafComplex (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).X n) E hcover B τ χ h

private theorem commonSpanHom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (B : CochainComplex (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over W)) ℤ)
    (τ χ : restrictedModel O K ε m hm U W a r f ⟶ B)
    (h : ∀ (n : ℤ) (X : (Over W)ᵒᵖ), E X →
      ∀ x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n).obj ((Over.map a).op.obj X),
      (τ.f n).val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (χ.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x)) : τ = χ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact commonSpanHom_ext_degree O K ε m hm U W a r f n
    E hcover (B.X n) (τ.f n) (χ.f n) (h n)

private def sheafModelAugmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ((ringFamilySheafModel O K ε m hm r f).1.X 0) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (ringFamilySheafModel O K ε m hm r f).2.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom

private theorem sheafModelAugmentationZero_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (X : Cᵒᵖ) (x : ((ringFamilyPresheafComplex O K ε m hm r f).X 0).obj X) :
    (sheafModelAugmentationZero O K ε m hm r f).val.app X
      ((modelUnit O K ε m hm r f 0).app X x) =
      ringComplexAugmentationValue (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x := by
  have h := ringFamilySheafModel_augmentation_unit O K ε m hm r f 0 X x
  have h' := congrArg
    (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).hom).val.app X)
    h
  change _ = _ at h'
  simp only [ringFamilyPresheafAugmentation,
    HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    Iso.app_inv, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    Category.assoc, ringFamilyPresheafAugmentationZero] at h'
  let y := ringComplexAugmentationValue
    (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x
  have hc := congrArg (fun z ↦ z.val.app X y)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv_hom_id)
  exact h'.trans hc

private theorem singleRestrictionAugmentation
    {D E : Type u} [Category D] [Category E] [HasZeroMorphisms D] [HasZeroObject D]
    [HasZeroMorphisms E] [HasZeroObject E]
    (F : D ⥤ E) [F.PreservesZeroMorphisms] (X : D)
    (L : CochainComplex E ℤ)
    (α : L ⟶ (HomologicalComplex.single E (.up ℤ) 0).obj (F.obj X)) :
    ((α ≫ ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv).f 0) ≫
      F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
      α.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj X)).hom := by
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let e' := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj X)
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Iso.app_inv]
  change (α.f 0 ≫ e'.hom ≫ F.map e.inv) ≫ F.map e.hom = α.f 0 ≫ e'.hom
  have hc : F.map e.inv ≫ F.map e.hom = 𝟙 _ := (F.mapIso e).inv_hom_id
  simp only [Category.assoc, hc, Category.comp_id]

private theorem singleRestrictionAugmentationIso
    {D E : Type u} [Category D] [Category E] [HasZeroMorphisms D] [HasZeroObject D]
    [HasZeroMorphisms E] [HasZeroObject E]
    (F : D ⥤ E) [F.PreservesZeroMorphisms] (X : D) (Y : E) (e : F.obj X ≅ Y)
    (L : CochainComplex E ℤ) (α : L ⟶ (HomologicalComplex.single E (.up ℤ) 0).obj Y) :
    ((α ≫ (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X) ≪≫
      (HomologicalComplex.single E (.up ℤ) 0).mapIso e).inv).f 0) ≫
        F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom =
      α.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫ e.inv := by
  rw [Iso.trans_inv, ← Category.assoc]
  change (((α ≫ (HomologicalComplex.single E (.up ℤ) 0).map e.inv) ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv).f 0) ≫
      F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom = _
  rw [singleRestrictionAugmentation]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] HomologicalComplex.single

private theorem restrictedAugmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C)
    (L : ringedSiteComplex (O.over U)) (α : L ⟶ ringTarget (O.over U)) :
    ((α ≫ ringRestrictionInv O U).f 0) ≫
      restrictedRingZeroProjection O U =
      α.f 0 ≫ ringZeroProjection (O.over U) := by
  dsimp only [ringRestrictionInv, restrictedRingZeroProjection, ringZeroProjection]
  have h := @singleRestrictionAugmentationIso _ _ _ _ _ _ _ _
    (SheafOfModules.overFunctor
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U)
    ⟨by intro M N; ext X x; rfl⟩
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (SheafOfModules.unit
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))
    (ringedOverRingIso O U) L α
  change ((α ≫ (ringedRestrictionRingComplexIso O U).inv).f 0) ≫ _ =
    α.f 0 ≫ _ ≫ (ringedOverRingIso O U).inv at h
  dsimp only [ringedOverRingIso, Iso.refl_inv] at h
  exact h.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))

private def sliceAugmentationToUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) (U : C)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    (sliceModelComplex O K ε m hm U r f).X 0 ⟶
      SheafOfModules.unit
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U) :=
  (sliceAugmentation O K ε m hm U r f).f 0 ≫ restrictedRingZeroProjection O U

private theorem sliceAugmentationToUnit_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) (U : C)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) (X : (Over U)ᵒᵖ)
    (x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).X 0).obj X) :
    (sliceAugmentationToUnit O K ε m hm U r f).val.app X
      ((sliceUnit O K ε m hm U r f 0).app X x) =
      ringComplexAugmentationValue
        (ε ((O.over U).obj.obj X) (ringFamilySectionIdeal (O.over U) r
          (fun i ↦ ringedSliceSection O U (f i)) X)) x := by
  have hzero := restrictedAugmentationZero O U
    (ringFamilySheafModel (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).1
    (ringFamilySheafModel (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).2
  have h := congrArg (fun τ ↦ τ.val.app X
    ((modelUnit (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i)) 0).app X x)) hzero
  have hunit := sheafModelAugmentationZero_unit (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i)) X x
  have ht := h.trans hunit
  dsimp only [sliceAugmentationToUnit, sliceAugmentation, sliceUnit, modelUnit,
    unitToSheaf, sheafModelAugmentationZero, ringZeroProjection]
  change @Eq ((O.over U).obj.obj X) _ _ at ht ⊢
  exact ht

attribute [local irreducible] ringFamilySheafModel

private theorem commonSpanCanonical_augmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) :
    let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
    (q.hom.f 0) ≫ (directOverMap R b).map
        (sliceAugmentationToUnit O K ε m hm V s g) ≫
        (directOverMapUnitIso (R := R) b).hom =
      (directOverMap R a).map
        (sliceAugmentationToUnit O K ε m hm U r f) ≫
        (directOverMapUnitIso (R := R) a).hom := by
  dsimp only
  apply commonSpanHom_ext_degree O K ε m hm U W a r f 0
    (fun X ↦ ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
      ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
    hcover
  intro X hX x
  change (sliceAugmentationToUnit O K ε m hm V s g).val.app ((Over.map b).op.obj X)
      ((q.hom.f 0).val.app X ((sliceUnit O K ε m hm U r f 0).app
        ((Over.map a).op.obj X) x)) = _
  rw [hq 0 X hX x]
  have hb := sliceAugmentationToUnit_unit O K ε m hm V s g ((Over.map b).op.obj X)
      (familyTransport K ((O.over W).obj.obj X) _ _ hX 0 x)
  have ha := sliceAugmentationToUnit_unit O K ε m hm U r f ((Over.map a).op.obj X) x
  have ht (A : CommRingCat.{u}) (I I' : {I : Ideal A // I.FG}) (h : I = I')
      (y : familyComponent K A I 0) :
      ringComplexAugmentationValue (ε A I') (familyTransport K A I I' h 0 y) =
        ringComplexAugmentationValue (ε A I) y := by
    subst I'
    rfl
  exact hb.trans ((ht _ _ _ hX x).trans ha.symm)

private theorem componentEquiv_trans
    {R : Type u} [Ring R] {ι : Type u} (P : ι → ModuleCat.{u} R)
    {I L M : ι} (h : I = L) (k : L = M) (x : P I) :
    (eqToIso (congrArg P (h.trans k))).toLinearEquiv x =
      (eqToIso (congrArg P k)).toLinearEquiv
        ((eqToIso (congrArg P h)).toLinearEquiv x) := by
  subst L
  subst M
  rfl

private theorem commonSpanCanonical_cocycle
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V T W : C) (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (r s t : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (h : Fin t → O.obj.obj (op T))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (z : restrictedModel O K ε m hm V W b s g ≅ restrictedModel O K ε m hm T W c t h)
    (v : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm T W c t h)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hz : commonSpanCanonical O K ε m hm V T W b c s t g h z)
    (hv : commonSpanCanonical O K ε m hm U T W a c r t f h v)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) ∧
        (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y) =
          ringFamilySectionIdeal (O.over W) t (commonSpanSections O T W c t h) (op Y))) :
    v.hom = q.hom ≫ z.hom := by
  apply commonSpanHom_ext O K ε m hm U W a r f
    (fun X ↦
      (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
        ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X) ∧
      (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X =
        ringFamilySectionIdeal (O.over W) t (commonSpanSections O T W c t h) X))
    hcover (restrictedModel O K ε m hm T W c t h)
  intro n X hx x
  change (v.hom.f n).val.app X _ =
    (z.hom.f n).val.app X ((q.hom.f n).val.app X _)
  have ht := componentEquiv_trans
    (fun I ↦ familyComponent K ((O.over W).obj.obj X) I n) hx.1 hx.2 x
  exact (hv n X (hx.1.trans hx.2) x).trans
    ((congrArg ((sliceUnit O K ε m hm T t h n).app ((Over.map c).op.obj X)) ht).trans
      ((hz n X hx.2 (familyTransport K ((O.over W).obj.obj X) _ _ hx.1 n x)).symm.trans
        (congrArg ((z.hom.f n).val.app X) (hq n X hx.1 x)).symm))

private theorem exists_commonSpanCoherentComparisons
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    {A : Type u} (U : A → C) (r : A → ℕ)
    (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t)))) :
    ∃ q : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      restrictedModel O K ε m hm (U i) W a (r i) (f i) ≅
        restrictedModel O K ε m hm (U j) W b (r j) (f j),
      (∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
        commonSpanCanonical O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
          (q i j W a b)) ∧
      (∀ (i j k : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) (c : W ⟶ U k),
        (q i k W a c).hom = (q i j W a b).hom ≫ (q j k W b c).hom) := by
  classical
  have hlocal (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) :
      ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
        ∀ (Z : C) (k : Z ⟶ T), S k →
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f i t))) =
            Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (f j t))) := by
    intro T h
    simpa only [Category.assoc] using heq i j T (h ≫ a) (h ≫ b)
  have hh := fun (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) ↦
    commonSpanModels_iso O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
      (hlocal i j W a b)
  choose q hq using hh
  refine ⟨q, hq, ?_⟩
  intro i j k W a b c
  apply commonSpanCanonical_cocycle O K ε m hm (U i) (U j) (U k) W a b c
    (r i) (r j) (r k) (f i) (f j) (f k)
    (q i j W a b) (q j k W b c) (q i k W a c)
    (hq i j W a b) (hq j k W b c) (hq i k W a c)
  intro X
  obtain ⟨S, hS, hs⟩ := commonSpanEqualityCover O (U i) (U j) W a b
    (r i) (r j) (f i) (f j) (hlocal i j W a b) X
  obtain ⟨T, hT, ht⟩ := commonSpanEqualityCover O (U j) (U k) W b c
    (r j) (r k) (f j) (f k) (hlocal j k W b c) X
  exact ⟨S ⊓ T, (J.over W).intersection_covering hS hT,
    fun Y v hv ↦ ⟨hs Y v hv.1, ht Y v hv.2⟩⟩

private theorem spanEvaluationEquiv_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (x : ((directOverMap R a).obj
      (SheafOfModules.unit (R.over U))).val.obj (op (Over.mk (𝟙 W)))) :
    spanEvaluationEquiv R a (SheafOfModules.unit (R.over U)) x = x := by
  rfl

private theorem spanTransitionEquiv_augmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (α : M.X 0 ⟶ SheafOfModules.unit (R.over U))
    (β : N.X 0 ⟶ SheafOfModules.unit (R.over V))
    (h : q.hom.f 0 ≫ (directOverMap R b).map β ≫
        (directOverMapUnitIso (R := R) b).hom =
      (directOverMap R a).map α ≫
        (directOverMapUnitIso (R := R) a).hom)
    (x : (M.X 0).val.obj (op (Over.mk a))) :
    β.val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q 0 x) =
      α.val.app (op (Over.mk a)) x := by
  change @Eq (R.obj.obj (op W)) _ _
  let y : ((directOverMap R a).obj (M.X 0)).val.obj
      (op (Over.mk (𝟙 W))) := (spanEvaluationEquiv R a (M.X 0)).symm x
  have hh := congrArg (fun z ↦ z.val.app (op (Over.mk (𝟙 W))) y) h
  have ha := spanEvaluationEquiv_naturality R a _ _ α y
  have hb := spanEvaluationEquiv_naturality R b _ _ β
    ((q.hom.f 0).val.app (op (Over.mk (𝟙 W))) y)
  change @Eq (R.obj.obj (op W)) _ _ at ha hb hh
  simp only [spanEvaluationEquiv_unit] at ha hb
  change ((directOverMap R b).map β).val.app (op (Over.mk (𝟙 W)))
    ((q.hom.f 0).val.app (op (Over.mk (𝟙 W))) y) =
      ((directOverMap R a).map α).val.app (op (Over.mk (𝟙 W))) y at hh
  have ha' : ((directOverMap R a).map α).val.app
      (op (Over.mk (𝟙 W))) y = α.val.app (op (Over.mk a)) x := by
    change @Eq (R.obj.obj (op W)) _ _
    simpa only [y, LinearEquiv.apply_symm_apply] using ha
  have hh' : ((directOverMap R b).map β).val.app
      (op (Over.mk (𝟙 W))) ((q.hom.f 0).val.app (op (Over.mk (𝟙 W))) y) =
        α.val.app (op (Over.mk a)) x := by
    change @Eq (R.obj.obj (op W)) _ _
    calc
      _ = ((directOverMap R a).map α).val.app
          (op (Over.mk (𝟙 W))) y := hh
      _ = _ := ha'
  exact hb.symm.trans hh'

private def arrowEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C}
    (M : SheafOfModules.{u} (R.over U)) {a b : W ⟶ U} (h : a = b) :
    (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk a))) ≃ₗ[
      R.obj.obj (op W)]
      (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk b))) :=
  (eqToIso (congrArg (fun c : W ⟶ U ↦
    (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk c)))) h)).toLinearEquiv

private theorem arrowEquiv_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W V : C}
    (M : SheafOfModules.{u} (R.over U)) (k : V ⟶ W)
    {a a' : W ⟶ U} {b b' : V ⟶ U} (ha : a = a') (hb : b = b')
    (hk : k ≫ a = b) (hk' : k ≫ a' = b')
    (x : M.val.obj (op (Over.mk a))) :
    arrowEquiv R M hb
      (M.val.map (Over.homMk (U := Over.mk b) (V := Over.mk a) k hk).op x) =
      M.val.map (Over.homMk (U := Over.mk b') (V := Over.mk a') k hk').op
        (arrowEquiv R M ha x) := by
  subst a'
  subst b'
  rfl

private theorem overMap_homMk_map_apply
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W T S : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) (v : T ⟶ W) (v' : S ⟶ W)
    (k : S ⟶ T) (hv : k ≫ v = v')
    (x : M.val.obj (op (Over.mk (v ≫ a)))) :
    ((directOverMap R a).obj M).val.map
      (Over.homMk (U := Over.mk v') (V := Over.mk v) k hv).op x =
      M.val.map (Over.homMk (U := Over.mk (v' ≫ a)) (V := Over.mk (v ≫ a)) k
        (by simpa only [Over.mk_hom, ← Category.assoc] using
          congrArg (fun t ↦ t ≫ a) hv)).op x := by
  change M.val.map ((Over.map a).map
    (Over.homMk (U := Over.mk v') (V := Over.mk v) k hv)).op x = _
  exact M.val.congr_map_apply (congrArg Quiver.Hom.op (by ext; rfl)) x

private theorem assoc_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W V : C} (a : W ⟶ U) (k : V ⟶ W)
    (M : SheafOfModules.{u} (R.over U)) (X Y : Over V) (h : Y ⟶ X)
    (x : M.val.obj (op (Over.mk ((X.hom ≫ k) ≫ a)))) :
    arrowEquiv R M (Category.assoc Y.hom k a)
      (M.val.map (((Over.map k ⋙ Over.map a).map h)).op x) =
        M.val.map (((Over.map (k ≫ a)).map h)).op
          (arrowEquiv R M (Category.assoc X.hom k a) x) :=
  arrowEquiv_naturality R M h.left
    (Category.assoc X.hom k a) (Category.assoc Y.hom k a)
    (by simp only [← Category.assoc, Over.w h])
    (by simp only [← Category.assoc, Over.w h]) x

private def spanAssocIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W V : C} (a : W ⟶ U) (k : V ⟶ W)
    (M : SheafOfModules.{u} (R.over U)) :
    (directOverMap R k).obj ((directOverMap R a).obj M) ≅
      (directOverMap R (k ≫ a)).obj M :=
  sheafIsoOfComponents (R.over V) _ _
    (fun X ↦ (arrowEquiv R M (Category.assoc X.unop.hom k a)).toModuleIso)
    (fun X Y h ↦ by
      ext x
      exact assoc_naturality R a k M X.unop Y.unop h.unop x)

private theorem spanTransport_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W T S : C}
    (a : W ⟶ U) (b : W ⟶ V)
    (M : SheafOfModules.{u} (R.over U)) (N : SheafOfModules.{u} (R.over V))
    (τ : (directOverMap R a).obj M ⟶ (directOverMap R b).obj N)
    (v : T ⟶ W) (v' : S ⟶ W) (k : S ⟶ T) (hv : k ≫ v = v')
    (c : T ⟶ U) (d : T ⟶ V) (c' : S ⟶ U) (d' : S ⟶ V)
    (hc : v ≫ a = c) (hd : v ≫ b = d)
    (hc' : v' ≫ a = c') (hd' : v' ≫ b = d')
    (hkc : k ≫ c = c') (hkd : k ≫ d = d')
    (x : M.val.obj (op (Over.mk c))) :
    arrowEquiv R N hd'
      (τ.val.app (op (Over.mk v')) ((arrowEquiv R M hc').symm
        (M.val.map (Over.homMk (U := Over.mk c') (V := Over.mk c) k hkc).op x))) =
      N.val.map (Over.homMk (U := Over.mk d') (V := Over.mk d) k hkd).op
        (arrowEquiv R N hd (τ.val.app (op (Over.mk v))
          ((arrowEquiv R M hc).symm x))) := by
  let y : M.val.obj (op (Over.mk (v ≫ a))) := (arrowEquiv R M hc).symm x
  have ha := arrowEquiv_naturality R M k hc hc'
    (by rw [← Category.assoc, hv]) hkc y
  have hb := arrowEquiv_naturality R N k hd hd'
    (by rw [← Category.assoc, hv]) hkd (τ.val.app (op (Over.mk v)) y)
  have ht := PresheafOfModules.naturality_apply τ.val
    (Over.homMk (U := Over.mk v') (V := Over.mk v) k hv).op y
  have hi : (arrowEquiv R M hc').symm
      (M.val.map (Over.homMk (U := Over.mk c') (V := Over.mk c) k hkc).op x) =
      ((directOverMap R a).obj M).val.map
        (Over.homMk (U := Over.mk v') (V := Over.mk v) k hv).op y := by
    apply (arrowEquiv R M hc').injective
    simpa only [LinearEquiv.apply_symm_apply, y, overMap_homMk_map_apply] using ha.symm
  rw [hi]
  exact (congrArg (arrowEquiv R N hd') ht).trans
    (by simpa only [overMap_homMk_map_apply, y] using hb)

private theorem arrowEquiv_trans
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (M : SheafOfModules.{u} (R.over U))
    {a b c : W ⟶ U} (h : a = b) (h' : b = c)
    (x : M.val.obj (op (Over.mk a))) :
    arrowEquiv R M h' (arrowEquiv R M h x) = arrowEquiv R M (h.trans h') x := by
  subst b
  subst c
  rfl

private theorem arrowEquiv_symm
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (M : SheafOfModules.{u} (R.over U))
    {a b : W ⟶ U} (h : a = b) (x : M.val.obj (op (Over.mk b))) :
    (arrowEquiv R M h).symm x = arrowEquiv R M h.symm x := by
  subst b
  rfl

private theorem arrowEquiv_overMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W V : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) {v v' : V ⟶ W} (h : v = v')
    (x : M.val.obj (op (Over.mk (v ≫ a)))) :
    arrowEquiv R ((directOverMap R a).obj M) h x =
      arrowEquiv R M (congrArg (fun t ↦ t ≫ a) h) x := by
  subst v'
  rfl

private theorem arrowEquiv_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C}
    (M N : SheafOfModules.{u} (R.over U)) (τ : M ⟶ N)
    {a b : W ⟶ U} (h : a = b) (x : M.val.obj (op (Over.mk a))) :
    arrowEquiv R N h (τ.val.app (op (Over.mk a)) x) =
      τ.val.app (op (Over.mk b)) (arrowEquiv R M h x) := by
  subst b
  rfl

private theorem spanTransition_conjugate
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W T : C} (a : W ⟶ U) (b : W ⟶ V)
    (k : T ⟶ W)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (q' : ((directOverMap R (k ≫ a)).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R (k ≫ b)).mapHomologicalComplex (.up ℤ)).obj N)
    (n : ℤ)
    (he : q'.hom.f n = (spanAssocIso R a k (M.X n)).inv ≫
      (directOverMap R k).map (q.hom.f n) ≫
        (spanAssocIso R b k (N.X n)).hom)
    (x : (M.X n).val.obj (op (Over.mk (k ≫ a)))) :
    spanTransitionEquiv R (k ≫ a) (k ≫ b) M N q' n x =
      (q.hom.f n).val.app (op (Over.mk k)) x := by
  change spanEvaluationEquiv R (k ≫ b) (N.X n)
    ((q'.hom.f n).val.app (op (Over.mk (𝟙 T)))
      ((spanEvaluationEquiv R (k ≫ a) (M.X n)).symm x)) = _
  rw [he]
  change arrowEquiv R (N.X n) (Category.id_comp (k ≫ b))
    (arrowEquiv R (N.X n) (Category.assoc (𝟙 T) k b)
      ((q.hom.f n).val.app (op (Over.mk ((𝟙 T) ≫ k)))
        ((arrowEquiv R (M.X n) (Category.assoc (𝟙 T) k a)).symm
          ((arrowEquiv R (M.X n) (Category.id_comp (k ≫ a))).symm x)))) = _
  have hh := arrowEquiv_hom R ((directOverMap R a).obj (M.X n))
    ((directOverMap R b).obj (N.X n)) (q.hom.f n) (Category.id_comp k)
    ((arrowEquiv R (M.X n) (congrArg (fun t ↦ t ≫ a) (Category.id_comp k))).symm x)
  simp only [arrowEquiv_overMap, LinearEquiv.apply_symm_apply] at hh
  simp only [arrowEquiv_symm, arrowEquiv_trans]
  change arrowEquiv R (N.X n) (congrArg (fun t ↦ t ≫ b) (Category.id_comp k))
    ((q.hom.f n).val.app (op (Over.mk ((𝟙 T) ≫ k)))
      (arrowEquiv R (M.X n) (congrArg (fun t ↦ t ≫ a)
        (Category.id_comp k)).symm x)) = _
  exact hh

private theorem spanTransition_naturality_of_conjugate
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W T : C} (a : W ⟶ U) (b : W ⟶ V)
    (k : T ⟶ W)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (q' : ((directOverMap R (k ≫ a)).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R (k ≫ b)).mapHomologicalComplex (.up ℤ)).obj N)
    (n : ℤ)
    (he : q'.hom.f n = (spanAssocIso R a k (M.X n)).inv ≫
      (directOverMap R k).map (q.hom.f n) ≫
        (spanAssocIso R b k (N.X n)).hom)
    (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R (k ≫ a) (k ≫ b) M N q' n
      ((M.X n).val.map
        (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
      (N.X n).val.map
        (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
          (spanTransitionEquiv R a b M N q n x) := by
  rw [spanTransition_conjugate R a b k M N q q' n he]
  have hh := spanTransport_naturality R a b (M.X n) (N.X n) (q.hom.f n)
    (𝟙 W) k k (Category.comp_id k) a b (k ≫ a) (k ≫ b)
    (Category.id_comp a) (Category.id_comp b) rfl rfl rfl rfl x
  change (q.hom.f n).val.app (op (Over.mk k))
    ((M.X n).val.map
      (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
        (N.X n).val.map
          (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
            (arrowEquiv R (N.X n) (Category.id_comp b)
              ((q.hom.f n).val.app (op (Over.mk (𝟙 W)))
                ((arrowEquiv R (M.X n) (Category.id_comp a)).symm x)))
  exact hh
attribute [local irreducible] spanTransitionEquiv spanEvaluationEquiv

private theorem canonical_at_arrows
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m)
    {U V W T : C} (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (n : ℤ) (v : T ⟶ W) (c : T ⟶ U) (d : T ⟶ V)
    (hc : v ≫ a = c) (hd : v ≫ b = d)
    (h : ringFamilySectionIdeal (O.over U) r
        (fun i ↦ ringedSliceSection O U (f i)) (op (Over.mk c)) =
      ringFamilySectionIdeal (O.over V) s
        (fun i ↦ ringedSliceSection O V (g i)) (op (Over.mk d)))
    (x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))).X n).obj (op (Over.mk c))) :
    arrowEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      ((sliceModelComplex O K ε m hm V s g).X n) hd
      ((q.hom.f n).val.app (op (Over.mk v))
        ((arrowEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
          ((sliceModelComplex O K ε m hm U r f).X n) hc).symm
            ((sliceUnit O K ε m hm U r f n).app (op (Over.mk c)) x))) =
      (sliceUnit O K ε m hm V s g n).app (op (Over.mk d))
        (familyTransport K (O.obj.obj (op T)) _ _ h n x) := by
  subst c
  subst d
  exact hq n (op (Over.mk v)) h x

private theorem ringFamily_idealDescent_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) {A : Type u} (U : A → C)
    (r : A → ℕ) (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t))))
    (q : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      restrictedModel O K ε m hm (U i) W a (r i) (f i) ≅
        restrictedModel O K ε m hm (U j) W b (r j) (f j))
    (hq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      commonSpanCanonical O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
        (q i j W a b)) :
    ∀ (n : ℤ) (i j : A) (W V : C) (k : V ⟶ W)
      (a : W ⟶ U i) (b : W ⟶ U j)
      (x : ((sliceModelComplex O K ε m hm (U i) (r i) (f i)).X n).val.obj
        (op (Over.mk a))),
      spanTransitionEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
        (k ≫ a) (k ≫ b) (sliceModelComplex O K ε m hm (U i) (r i) (f i))
        (sliceModelComplex O K ε m hm (U j) (r j) (f j))
        (q i j V (k ≫ a) (k ≫ b)) n
        (((sliceModelComplex O K ε m hm (U i) (r i) (f i)).X n).val.map
          (Over.homMk (U := Over.mk (k ≫ a)) (V := Over.mk a) k rfl).op x) =
      ((sliceModelComplex O K ε m hm (U j) (r j) (f j)).X n).val.map
        (Over.homMk (U := Over.mk (k ≫ b)) (V := Over.mk b) k rfl).op
          (spanTransitionEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
            a b (sliceModelComplex O K ε m hm (U i) (r i) (f i))
            (sliceModelComplex O K ε m hm (U j) (r j) (f j)) (q i j W a b) n x) := by
  intro n i j W V k a b x
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let M := sliceModelComplex O K ε m hm (U i) (r i) (f i)
  let N := sliceModelComplex O K ε m hm (U j) (r j) (f j)
  let ea := spanAssocIso R a k (M.X n)
  let eb := spanAssocIso R b k (N.X n)
  have he : (q i j V (k ≫ a) (k ≫ b)).hom.f n =
      ea.inv ≫ (directOverMap R k).map ((q i j W a b).hom.f n) ≫ eb.hom := by
    apply commonSpanHom_ext_degree O K ε m hm (U i) V (k ≫ a) (r i) (f i) n
      (fun X ↦ ringFamilySectionIdeal (O.over V) (r i)
          (commonSpanSections O (U i) V (k ≫ a) (r i) (f i)) X =
        ringFamilySectionIdeal (O.over V) (r j)
          (commonSpanSections O (U j) V (k ≫ b) (r j) (f j)) X)
    · apply commonSpanEqualityCover O (U i) (U j) V (k ≫ a) (k ≫ b)
        (r i) (r j) (f i) (f j)
      intro T h
      simpa only [Category.assoc] using heq i j T (h ≫ k ≫ a) (h ≫ k ≫ b)
    · intro X hX y
      exact (hq i j V (k ≫ a) (k ≫ b) n X hX y).trans
        (canonical_at_arrows O K ε m hm a b (r i) (r j) (f i) (f j)
          (q i j W a b) (hq i j W a b) n (X.unop.hom ≫ k)
          (X.unop.hom ≫ k ≫ a) (X.unop.hom ≫ k ≫ b)
          (Category.assoc X.unop.hom k a) (Category.assoc X.unop.hom k b) hX y).symm
  exact spanTransition_naturality_of_conjugate R a b k M N (q i j W a b)
    (q i j V (k ≫ a) (k ≫ b)) n he x

private theorem section_iso_injective
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (W : C) {x y : M.val.obj (op W)}
    (h : e.hom.val.app (op W) x = e.hom.val.app (op W) y) : x = y :=
  (((SheafOfModules.evaluation R (op W)).mapIso e).toLinearEquiv).injective h

private theorem spanTransitionEquiv_toSingle
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((directOverMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((directOverMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (X : SheafOfModules.{u} R)
    (α : M ⟶ ((SheafOfModules.overFunctor R U).mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj X))
    (β : N ⟶ ((SheafOfModules.overFunctor R V).mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single _ (.up ℤ) 0).obj X))
    (h : ∀ x : (M.X 0).val.obj (op (Over.mk a)),
      (β.f 0 ≫ (SheafOfModules.overFunctor R V).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).val.app (op (Over.mk b))
          (spanTransitionEquiv R a b M N q 0 x) =
      (α.f 0 ≫ (SheafOfModules.overFunctor R U).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).val.app (op (Over.mk a)) x)
    (n : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    (β.f n).val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q n x) =
      (α.f n).val.app (op (Over.mk a)) x := by
  by_cases hn : n = 0
  · subst n
    apply section_iso_injective R (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X) W
    exact h x
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X n hn
    have ha := Functor.map_isZero (SheafOfModules.overFunctor R U) hz
    have hb := Functor.map_isZero (SheafOfModules.overFunctor R V) hz
    rw [ha.eq_zero_of_tgt (α.f n), hb.eq_zero_of_tgt (β.f n)]
    rfl

/-- The canonical transition maps commute with the specified augmentations.
Source: Stacks Project, Tag 099E, augmentation compatibility of the canonical
identifications. The proof is obtained by evaluating the degree-zero comparison on
unit sections and using the single-complex augmentation, with zero target components
in every other degree.
(auxiliary; not a blueprint node). -/
private theorem ringFamily_idealDescent_augmentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (K : RingComplexFamily.{u})
    (ε : RingComplexAugmentations K) (m : RingComplexMaps K)
    (hm : RingComplexFunctorial K ε m) {A : Type u} (U : A → C)
    (r : A → ℕ) (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t))))
    (q : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      restrictedModel O K ε m hm (U i) W a (r i) (f i) ≅
        restrictedModel O K ε m hm (U j) W b (r j) (f j))
    (hq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      commonSpanCanonical O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
        (q i j W a b)) :
    ∀ (n : ℤ) (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j)
      (x : ((sliceModelComplex O K ε m hm (U i) (r i) (f i)).X n).val.obj
        (op (Over.mk a))),
      ((sliceAugmentation O K ε m hm (U j) (r j) (f j)).f n).val.app
            (op (Over.mk b))
        (spanTransitionEquiv ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
          a b (sliceModelComplex O K ε m hm (U i) (r i) (f i))
          (sliceModelComplex O K ε m hm (U j) (r j) (f j)) (q i j W a b) n x) =
      ((sliceAugmentation O K ε m hm (U i) (r i) (f i)).f n).val.app
            (op (Over.mk a)) x := by
  intro n i j W a b x
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  refine spanTransitionEquiv_toSingle R a b _ _ (q i j W a b)
    (SheafOfModules.unit R)
    (sliceAugmentation O K ε m hm (U i) (r i) (f i))
    (sliceAugmentation O K ε m hm (U j) (r j) (f j)) ?_ n x
  intro x
  have hlocal : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (f j t))) := by
    intro T h
    simpa only [Category.assoc] using heq i j T (h ≫ a) (h ≫ b)
  have haug := commonSpanCanonical_augmentationZero O K ε m hm
    (U i) (U j) W a b (r i) (r j) (f i) (f j) (q i j W a b)
    (hq i j W a b)
    (commonSpanEqualityCover O (U i) (U j) W a b (r i) (r j) (f i) (f j) hlocal)
  have hh := spanTransitionEquiv_augmentationZero
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a b
    (sliceModelComplex O K ε m hm (U i) (r i) (f i))
    (sliceModelComplex O K ε m hm (U j) (r j) (f j)) (q i j W a b)
    (sliceAugmentationToUnit O K ε m hm (U i) (r i) (f i))
    (sliceAugmentationToUnit O K ε m hm (U j) (r j) (f j)) haug x
  change @Eq (O.obj.obj (op W)) _ _ at hh ⊢
  exact hh

-- Cached proof instances are local to the private implementation.
attribute [-instance] commRingToTypeCompose addCommGrpToTypeCompose
  abelianHasSheafify abelianLocalEquivalences
attribute [-instance] modulePreadditive presheafModulePreadditive moduleAddCommGroup
  moduleModule moduleHomCoe
attribute [-instance] commRingForgetHasSheafCompose moduleZeroObject moduleZeroMorphisms
  standardOverMap_preservesZero overFunctor_preservesZero
  overMap_preservesZero overMap_additive

/-- Locally equal section ideals give coherent strict descent data for the sheafified
ring-family complexes. This assertion has no ideal module, finite-type assumption,
covering-family assumption, derived category or Čech complex.
Source: Stacks Project, Tag 099E, the canonical identifications and their cocycle.
(auxiliary; not a blueprint node).

Proof: on a common test span, restrict both presheaf complexes to the slice of the test
object. The section ideals are equal on a restriction-stable locus which covers every
object, by the hypothesis applied to further test spans. On that locus identify the ring
complexes by transport along equality of their ideals. The construction
ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit gives the augmented chain isomorphism.
Use exists_ringFamilySheafModel_restrictionIso to identify its source and target with
restrictions of the original slice models. Its formula on sheafification-unit sections
specifies the transition map uniquely: sheafification_hom_ext_on_locus applies on the
same covering locus. Further restriction preserves this formula, so uniqueness gives
naturality. On a triple common span intersect the three equality loci; transport along
equality is transitive there, so uniqueness gives the cocycle. The chain equation is
supplied by the chain comparisons. For augmentation, test on unit
sections: the comparison sends a section to its transport along equality of ideals, and
the ring-family augmentation commutes with that transport. The sheafification adjunction
identifies these presheaf augmentations with the specified sheaf augmentations. The same
hom-ext theorem therefore proves the augmentation equation. Evaluate the resulting chain
isomorphisms at the terminal test object to obtain the specified linear transitions.
Empty indexing families and empty generating lists use the same formulas. -/
theorem exists_ringFamily_idealDescentData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    {A : Type u} (U : A → C) (r : A → ℕ)
    (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t)))) :
    Nonempty (SheafOfModules.AugmentedComplexGlueData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U (ringedSiteRingComplex O)
      (fun i ↦ (ringFamilySheafModel (O.over (U i)) K ε m hm (r i)
        (fun t ↦ ringedSliceSection O (U i) (f i t))).1)
      (fun i ↦ (ringFamilySheafModel (O.over (U i)) K ε m hm (r i)
        (fun t ↦ ringedSliceSection O (U i) (f i t))).2 ≫
          (ringedRestrictionRingComplexIso O (U i)).inv)) := by
  classical
  change Nonempty (SheafOfModules.AugmentedComplexGlueData
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U (ringTarget O)
    (fun i ↦ sliceModelComplex O K ε m hm (U i) (r i) (f i))
    (fun i ↦ sliceAugmentation O K ε m hm (U i) (r i) (f i)))
  obtain ⟨q, hq, hqc⟩ := exists_commonSpanCoherentComparisons O K ε m hm U r f heq
  have hn := ringFamily_idealDescent_naturality O K ε m hm U r f heq q hq
  have hα := ringFamily_idealDescent_augmentation O K ε m hm U r f heq q hq
  let d := glueDataOfComparisons
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U (ringTarget O)
    (fun i ↦ sliceModelComplex O K ε m hm (U i) (r i) (f i))
    (fun i ↦ sliceAugmentation O K ε m hm (U i) (r i) (f i)) q hqc hn hα
  exact ⟨d⟩

end CategoryTheory
