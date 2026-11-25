/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.Algebra.Homology.Localization

/-! # Derived squares under exact equivalences

Source: Stacks Tags 05RR and 0941.
(blueprint: lem-derived-exact-equivalence-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem rightKanExtension_precomp
    {C₀ C₁ D H : Type*} [Category* C₀] [Category* C₁] [Category* D] [Category* H]
    (P : C₀ ⥤ C₁) (L : C₁ ⥤ D) (F : C₁ ⥤ H) (K : D ⥤ H)
    (ε : L ⋙ K ⟶ F) [K.IsRightKanExtension ε]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Full]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Faithful] :
    K.IsRightKanExtension
      ((CategoryTheory.Functor.associator P L K).hom ≫
        CategoryTheory.Functor.whiskerLeft P ε) := by
  let G := CategoryTheory.Functor.RightExtension.precomp L F P
  have : G.IsEquivalence := by
    dsimp only [G, CategoryTheory.Functor.RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  dsimp [G, CategoryTheory.Functor.RightExtension.precomp,
    CategoryTheory.Functor.RightExtension.mk,
    CategoryTheory.Functor.whiskeringLeft]
  simp only [Category.id_comp, Category.comp_id]

private theorem rightKanExtension_postcomp
    {C D H H' : Type*} [Category* C] [Category* D] [Category* H] [Category* H']
    (L : C ⥤ D) (F : C ⥤ H) (K : D ⥤ H) (ε : L ⋙ K ⟶ F)
    [K.IsRightKanExtension ε] (e : H ≌ H') :
    (K ⋙ e.functor).IsRightKanExtension
      ((CategoryTheory.Functor.associator L K e.functor).inv ≫
        CategoryTheory.Functor.whiskerRight ε e.functor) := by
  let G := CategoryTheory.Functor.RightExtension.postcompose₂ L F e.functor
  have : G.IsEquivalence := by
    let α :
        (CategoryTheory.Functor.whiskeringRight D H H').obj e.functor ⋙
            (CategoryTheory.Functor.whiskeringLeft C D H').obj L ≅
          (CategoryTheory.Functor.whiskeringLeft C D H).obj L ⋙
            (CategoryTheory.Functor.whiskeringRight C H H').obj e.functor :=
      NatIso.ofComponents (fun (X : D ⥤ H) ↦
      (CategoryTheory.Functor.associator L X e.functor).symm) (by
        intro X Y f
        ext Z
        simp)
    change (CostructuredArrow.map₂ α.hom (𝟙 _)).IsEquivalence
    apply CostructuredArrow.isEquivalenceMap₂
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  exact ⟨⟨IsTerminal.ofIso h
    (CategoryTheory.Functor.RightExtension.postcompose₂ObjMkIso e.functor ε)⟩⟩

private theorem rightKanExtension_iso1
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {L L' : C ⥤ D} (e : L ≅ L') (F : C ⥤ H) (K : D ⥤ H)
    (ε : L ⋙ K ⟶ F) [K.IsRightKanExtension ε] :
    K.IsRightKanExtension
      ((CategoryTheory.Functor.isoWhiskerRight e K).inv ≫ ε) := by
  let G := (CategoryTheory.Functor.rightExtensionEquivalenceOfIso₁ e F).functor
  let : PreservesLimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalencePreservesLimits G).preservesLimitsOfShape.preservesLimit
  let : ReflectsLimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsLimits_of_isEquivalence G).reflectsLimitsOfShape.reflectsLimit
  have h := (IsTerminal.isTerminalIffObj G
    (CategoryTheory.Functor.RightExtension.mk K ε)).1
      (K.isUniversalOfIsRightKanExtension ε)
  refine ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  change (𝟙 _ ≫ K.map (e.inv.app X) ≫ ε.app X) =
    K.map (e.inv.app X) ≫ ε.app X
  rw [Category.id_comp]

private theorem leftKanExtension_precomp
    {C₀ C₁ D H : Type*} [Category* C₀] [Category* C₁] [Category* D] [Category* H]
    (P : C₀ ⥤ C₁) (L : C₁ ⥤ D) (F : C₁ ⥤ H) (K : D ⥤ H)
    (ε : F ⟶ L ⋙ K) [K.IsLeftKanExtension ε]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Full]
    [((CategoryTheory.Functor.whiskeringLeft C₀ C₁ H).obj P).Faithful] :
    K.IsLeftKanExtension
      (CategoryTheory.Functor.whiskerLeft P ε ≫
        (CategoryTheory.Functor.associator P L K).inv) := by
  let G := CategoryTheory.Functor.LeftExtension.precomp L F P
  have : G.IsEquivalence := by
    dsimp only [G, CategoryTheory.Functor.LeftExtension.precomp]
    apply StructuredArrow.isEquivalenceMap₂
  let : PreservesColimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalence_preservesColimits G).preservesColimitsOfShape.preservesColimit
  let : ReflectsColimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsColimits_of_isEquivalence G).reflectsColimitsOfShape
      |>.reflectsColimit
  have h := (IsInitial.isInitialIffObj G
    (CategoryTheory.Functor.LeftExtension.mk K ε)).1
      (K.isUniversalOfIsLeftKanExtension ε)
  refine ⟨⟨IsInitial.ofIso h (StructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  dsimp [G, CategoryTheory.Functor.LeftExtension.precomp,
    CategoryTheory.Functor.LeftExtension.mk,
    CategoryTheory.Functor.whiskeringLeft]
  simp only [Category.id_comp, Category.comp_id]

private theorem leftKanExtension_postcomp
    {C D H H' : Type*} [Category* C] [Category* D] [Category* H] [Category* H']
    (L : C ⥤ D) (F : C ⥤ H) (K : D ⥤ H) (ε : F ⟶ L ⋙ K)
    [K.IsLeftKanExtension ε] (e : H ≌ H') :
    (K ⋙ e.functor).IsLeftKanExtension
      (CategoryTheory.Functor.whiskerRight ε e.functor ≫
        (CategoryTheory.Functor.associator L K e.functor).hom) := by
  let G := CategoryTheory.Functor.LeftExtension.postcompose₂ L F e.functor
  have : G.IsEquivalence := by
    let β :
        (CategoryTheory.Functor.whiskeringLeft C D H).obj L ⋙
            (CategoryTheory.Functor.whiskeringRight C H H').obj e.functor ≅
          (CategoryTheory.Functor.whiskeringRight D H H').obj e.functor ⋙
            (CategoryTheory.Functor.whiskeringLeft C D H').obj L :=
      NatIso.ofComponents (fun (X : D ⥤ H) ↦
        CategoryTheory.Functor.associator L X e.functor) (by
          intro X Y f
          ext Z
          simp)
    change (StructuredArrow.map₂ (𝟙 _) β.hom).IsEquivalence
    apply StructuredArrow.isEquivalenceMap₂
  let : PreservesColimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalence_preservesColimits G).preservesColimitsOfShape.preservesColimit
  let : ReflectsColimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsColimits_of_isEquivalence G).reflectsColimitsOfShape
      |>.reflectsColimit
  have h := (IsInitial.isInitialIffObj G
    (CategoryTheory.Functor.LeftExtension.mk K ε)).1
      (K.isUniversalOfIsLeftKanExtension ε)
  exact ⟨⟨IsInitial.ofIso h
    (CategoryTheory.Functor.LeftExtension.postcompose₂ObjMkIso e.functor ε)⟩⟩

private theorem leftKanExtension_iso1
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {L L' : C ⥤ D} (e : L ≅ L') (F : C ⥤ H) (K : D ⥤ H)
    (ε : F ⟶ L ⋙ K) [K.IsLeftKanExtension ε] :
    K.IsLeftKanExtension
      (ε ≫ (CategoryTheory.Functor.isoWhiskerRight e K).hom) := by
  let G := (CategoryTheory.Functor.leftExtensionEquivalenceOfIso₁ e F).functor
  let : PreservesColimit (Functor.empty.{0} _) G :=
    (Adjunction.isEquivalence_preservesColimits G).preservesColimitsOfShape.preservesColimit
  let : ReflectsColimit (Functor.empty.{0} _) G :=
    (CategoryTheory.Functor.reflectsColimits_of_isEquivalence G).reflectsColimitsOfShape
      |>.reflectsColimit
  have h := (IsInitial.isInitialIffObj G
    (CategoryTheory.Functor.LeftExtension.mk K ε)).1
      (K.isUniversalOfIsLeftKanExtension ε)
  refine ⟨⟨IsInitial.ofIso h (StructuredArrow.isoMk (Iso.refl _) ?_)⟩⟩
  ext X
  change (ε.app X ≫ K.map (e.hom.app X)) ≫ 𝟙 _ =
    ε.app X ≫ K.map (e.hom.app X)
  rw [Category.comp_id]

section KanSquare
variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* H₁] [Category* H₂]
  (P : C₁ ≌ C₂) (E : D₁ ≌ D₂) (G : H₁ ≌ H₂)
  (L : C₁ ⥤ D₁) (L' : C₂ ⥤ D₂)
  (F : C₁ ⥤ H₁) (F' : C₂ ⥤ H₂)
  (K : D₁ ⥤ H₁) (K' : D₂ ⥤ H₂)
  (ε : L ⋙ K ⟶ F) (ε' : L' ⋙ K' ⟶ F')
  (eL : L ⋙ E.functor ≅ P.functor ⋙ L')
  (eF : F ⋙ G.functor ≅ P.functor ⋙ F')

private def kanSquareCounit : L ⋙ (E.functor ⋙ K') ⟶ P.functor ⋙ F' :=
  (CategoryTheory.Functor.associator _ _ _).inv ≫
    CategoryTheory.Functor.whiskerRight eL.hom K' ≫
      (CategoryTheory.Functor.associator _ _ _).hom ≫
        CategoryTheory.Functor.whiskerLeft P.functor ε'

private def kanSquarePostCounit : L ⋙ (K ⋙ G.functor) ⟶ F ⋙ G.functor :=
  (CategoryTheory.Functor.associator _ _ _).inv ≫
    CategoryTheory.Functor.whiskerRight ε G.functor

private theorem kanSquare_universal [K'.IsRightKanExtension ε'] :
    (E.functor ⋙ K').IsRightKanExtension (kanSquareCounit P E L L' F' K' ε' eL) := by
  have := rightKanExtension_precomp P.functor L' F' K' ε'
  exact (CategoryTheory.Functor.isRightKanExtension_iff_postcomp₁
    E.functor eL _).mp inferInstance

private def kanSquareIso [K.IsRightKanExtension ε] [K'.IsRightKanExtension ε'] :
    K ⋙ G.functor ≅ E.functor ⋙ K' := by
  have hpost : (K ⋙ G.functor).IsRightKanExtension
      (kanSquarePostCounit G L F K ε) := rightKanExtension_postcomp L F K ε G
  have := kanSquare_universal P E L L' F' K' ε' eL
  exact CategoryTheory.Functor.rightKanExtensionUniqueOfIso _
    (kanSquarePostCounit G L F K ε) eF _
      (kanSquareCounit P E L L' F' K' ε' eL)

private theorem kanSquareIso_fac [K.IsRightKanExtension ε] [K'.IsRightKanExtension ε'] :
    CategoryTheory.Functor.whiskerLeft L
        (kanSquareIso P E G L L' F F' K K' ε ε' eL eF).hom ≫
      kanSquareCounit P E L L' F' K' ε' eL =
        kanSquarePostCounit G L F K ε ≫ eF.hom := by
  have hpost : (K ⋙ G.functor).IsRightKanExtension
      (kanSquarePostCounit G L F K ε) := rightKanExtension_postcomp L F K ε G
  have := kanSquare_universal P E L L' F' K' ε' eL
  simp only [kanSquareIso,
    CategoryTheory.Functor.rightKanExtensionUniqueOfIso_hom,
    CategoryTheory.Functor.liftOfIsRightKanExtension_fac]
end KanSquare
attribute [local irreducible] kanSquareIso kanSquareCounit kanSquarePostCounit

section LeftKanSquare
variable {C₁ C₂ D₁ D₂ H₁ H₂ : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* H₁] [Category* H₂]
  (P : C₁ ≌ C₂) (E : D₁ ≌ D₂) (G : H₁ ≌ H₂)
  (L : C₁ ⥤ D₁) (L' : C₂ ⥤ D₂)
  (F : C₁ ⥤ H₁) (F' : C₂ ⥤ H₂)
  (K : D₁ ⥤ H₁) (K' : D₂ ⥤ H₂)
  (ε : F ⟶ L ⋙ K) (ε' : F' ⟶ L' ⋙ K')
  (eL : L ⋙ E.functor ≅ P.functor ⋙ L')
  (eF : F ⋙ G.functor ≅ P.functor ⋙ F')

private def leftKanSquareCounit : P.functor ⋙ F' ⟶ L ⋙ (E.functor ⋙ K') :=
  CategoryTheory.Functor.whiskerLeft P.functor ε' ≫
    (CategoryTheory.Functor.associator _ _ _).inv ≫
      CategoryTheory.Functor.whiskerRight eL.inv K' ≫
        (CategoryTheory.Functor.associator _ _ _).hom

private def leftKanSquarePostCounit : F ⋙ G.functor ⟶ L ⋙ (K ⋙ G.functor) :=
  CategoryTheory.Functor.whiskerRight ε G.functor ≫
    (CategoryTheory.Functor.associator _ _ _).hom

private theorem leftKanSquare_universal [K'.IsLeftKanExtension ε'] :
    (E.functor ⋙ K').IsLeftKanExtension (leftKanSquareCounit P E L L' F' K' ε' eL) := by
  let α := CategoryTheory.Functor.whiskerLeft P.functor ε' ≫
    (CategoryTheory.Functor.associator P.functor L' K').inv
  have : K'.IsLeftKanExtension α := leftKanExtension_precomp P.functor L' F' K' ε'
  simpa only [leftKanSquareCounit, α, Category.assoc] using
    (CategoryTheory.Functor.isLeftKanExtension_iff_postcomp₁
      E.functor eL α).mp inferInstance

private def leftKanSquareIso [K.IsLeftKanExtension ε] [K'.IsLeftKanExtension ε'] :
    K ⋙ G.functor ≅ E.functor ⋙ K' := by
  have hpost : (K ⋙ G.functor).IsLeftKanExtension
      (leftKanSquarePostCounit G L F K ε) := leftKanExtension_postcomp L F K ε G
  have := leftKanSquare_universal P E L L' F' K' ε' eL
  exact CategoryTheory.Functor.leftKanExtensionUniqueOfIso _
    (leftKanSquarePostCounit G L F K ε) eF _
      (leftKanSquareCounit P E L L' F' K' ε' eL)

private theorem leftKanSquareIso_fac
    [K.IsLeftKanExtension ε] [K'.IsLeftKanExtension ε'] :
    leftKanSquarePostCounit G L F K ε ≫
        CategoryTheory.Functor.whiskerLeft L
          (leftKanSquareIso P E G L L' F F' K K' ε ε' eL eF).hom =
      eF.hom ≫ leftKanSquareCounit P E L L' F' K' ε' eL := by
  have hpost : (K ⋙ G.functor).IsLeftKanExtension
      (leftKanSquarePostCounit G L F K ε) := leftKanExtension_postcomp L F K ε G
  have := leftKanSquare_universal P E L L' F' K' ε' eL
  simp only [leftKanSquareIso,
    CategoryTheory.Functor.leftKanExtensionUniqueOfIso_hom,
    CategoryTheory.Functor.descOfIsLeftKanExtension_fac]
end LeftKanSquare
attribute [local irreducible] leftKanSquareIso leftKanSquareCounit leftKanSquarePostCounit

section CochainDerived
variable {B H : Type*} [Category* B] [Category* H] [Abelian B] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory H]
  (F : B ⥤ H) [F.Additive] (LF : DerivedCategory B ⥤ DerivedCategory H)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- Canonical identification between complex localization and homotopy localization
for the mapped additive functor.
Source: Stacks Tags 05RR and 0941.
(blueprint: def-derived-cochain-comparison-factors). -/
def derivedCochainComparisonFactors :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      HomotopyCategory.quotient B (.up ℤ) ⋙
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
  CategoryTheory.Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso H).symm ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
    CategoryTheory.Functor.associator _ _ _

/-- Transport a derived counit on homotopy categories to complex localization.
Source: Stacks Tags 05RR and 0941.
(blueprint: def-derived-cochain-counit). -/
def derivedCochainCounit : DerivedCategory.Q ⋙ LF ⟶
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (CategoryTheory.Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) LF).inv ≫
    (CategoryTheory.Functor.associator _ _ _).hom ≫
      CategoryTheory.Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) ε ≫
        (derivedCochainComparisonFactors F).inv

private theorem cochainCounit_universal
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] :
    LF.IsRightKanExtension (derivedCochainCounit F LF ε) := by
  have := CategoryTheory.Functor.IsLeftDerivedFunctor.isRightKanExtension LF ε
    (HomotopyCategory.quasiIso B (.up ℤ))
  have := rightKanExtension_precomp (HomotopyCategory.quotient B (.up ℤ))
    DerivedCategory.Qh _ LF ε
  have h := rightKanExtension_iso1 (DerivedCategory.quotientCompQhIso B) _ LF
    ((CategoryTheory.Functor.associator _ _ _).hom ≫
      CategoryTheory.Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) ε)
  exact (CategoryTheory.Functor.isRightKanExtension_iff_of_iso₂ _
    (derivedCochainCounit F LF ε) (derivedCochainComparisonFactors F).symm (Iso.refl _) (by
      simp only [derivedCochainCounit, Iso.symm_hom,
        Iso.refl_hom, CategoryTheory.Functor.whiskerLeft_id', Category.id_comp,
        Category.assoc])).mp h

private theorem cochainCounit_app_eq (P : CochainComplex B ℤ) :
    (derivedCochainCounit F LF ε).app P =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  simp only [derivedCochainCounit, derivedCochainComparisonFactors, NatTrans.comp_app,
    Iso.trans_inv,
    Iso.symm_inv, CategoryTheory.Functor.isoWhiskerRight_inv,
    CategoryTheory.Functor.isoWhiskerLeft_inv,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app,
    CategoryTheory.Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  change LF.map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Transport a derived unit on homotopy categories to complex localization.
Source: Stacks Tags 05RR and 0941.
(blueprint: def-derived-cochain-right-unit). -/
def derivedCochainRightUnit
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ LF) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LF :=
  (derivedCochainComparisonFactors F).hom ≫
    CategoryTheory.Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) η ≫
      (CategoryTheory.Functor.associator _ _ _).inv ≫
        (CategoryTheory.Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) LF).hom

private theorem cochainRightUnit_app_eq
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ LF) (P : CochainComplex B ℤ) :
    (derivedCochainRightUnit F LF η).app P =
      η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  simp only [derivedCochainRightUnit, derivedCochainComparisonFactors, NatTrans.comp_app,
    Iso.trans_hom,
    Iso.symm_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
    CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app,
    CategoryTheory.Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  change (𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ _ ≫ LF.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem cochainRightUnit_universal
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ LF)
    [LF.IsRightDerivedFunctor η (HomotopyCategory.quasiIso B (.up ℤ))] :
    LF.IsLeftKanExtension (derivedCochainRightUnit F LF η) := by
  have := CategoryTheory.Functor.IsRightDerivedFunctor.isLeftKanExtension LF η
    (HomotopyCategory.quasiIso B (.up ℤ))
  have := leftKanExtension_precomp (HomotopyCategory.quotient B (.up ℤ))
    DerivedCategory.Qh _ LF η
  have h := leftKanExtension_iso1 (DerivedCategory.quotientCompQhIso B) _ LF
    (CategoryTheory.Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) η ≫
      (CategoryTheory.Functor.associator _ _ _).inv)
  exact (CategoryTheory.Functor.isLeftKanExtension_iff_of_iso₂ _
    (derivedCochainRightUnit F LF η) (derivedCochainComparisonFactors F).symm (Iso.refl _) (by
      simp only [derivedCochainRightUnit, Iso.symm_hom, Iso.refl_hom,
        CategoryTheory.Functor.whiskerLeft_id', Category.comp_id, Category.assoc,
        Iso.inv_hom_id_assoc])).mp h

end CochainDerived

attribute [local irreducible] derivedCochainCounit derivedCochainComparisonFactors

private theorem leftDerivedSquare
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (ε : DerivedCategory.Q ⋙ LF ⟶
      L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ LF' ⟶
      L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [LF.IsRightKanExtension ε] [LF'.IsRightKanExtension ε']
    (e : L ⋙ G.functor ≅ E.functor ⋙ L') :
    ∃ φ : LF ⋙ G.mapDerivedCategory.functor ≅ E.mapDerivedCategory.functor ⋙ LF',
      ∀ P : CochainComplex B ℤ,
        φ.hom.app (DerivedCategory.Q.obj P) ≫
          LF'.map (E.functor.mapDerivedCategoryFactors.hom.app P) ≫
            ε'.app ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) =
          G.mapDerivedCategory.functor.map (ε.app P) ≫
            G.functor.mapDerivedCategoryFactors.hom.app
              ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  let P := E.mapHomologicalComplex (.up ℤ)
  let ED := E.mapDerivedCategory
  let GD := G.mapDerivedCategory
  let eF : (L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ GD.functor ≅
      P.functor ⋙ (L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    CategoryTheory.Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft _ G.functor.mapDerivedCategoryFactors ≪≫
        (CategoryTheory.Functor.associator _ _ _).symm ≪≫
          CategoryTheory.Functor.isoWhiskerRight
            (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (L ⋙ G.functor)) (.up ℤ) ≪≫
              NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
              (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (E.functor ⋙ L')) (.up ℤ)).symm) DerivedCategory.Q ≪≫
            CategoryTheory.Functor.associator _ _ _
  refine ⟨kanSquareIso P ED GD DerivedCategory.Q DerivedCategory.Q _ _ LF LF' ε ε'
    E.functor.mapDerivedCategoryFactors eF, ?_⟩
  intro X
  have h := NatTrans.congr_app
    (kanSquareIso_fac P ED GD DerivedCategory.Q DerivedCategory.Q _ _ LF LF' ε ε'
      E.functor.mapDerivedCategoryFactors eF) X
  simp only [kanSquareCounit, kanSquarePostCounit, eF, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_id,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Category.assoc] at h
  erw [Category.id_comp] at h
  exact h

private theorem rightDerivedSquare
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (ε : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LF)
    (ε' : L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LF')
    [LF.IsLeftKanExtension ε] [LF'.IsLeftKanExtension ε']
    (e : L ⋙ G.functor ≅ E.functor ⋙ L') :
    ∃ φ : LF ⋙ G.mapDerivedCategory.functor ≅ E.mapDerivedCategory.functor ⋙ LF',
      ∀ P : CochainComplex B ℤ,
        G.mapDerivedCategory.functor.map (ε.app P) ≫
          φ.hom.app (DerivedCategory.Q.obj P) ≫
            LF'.map (E.functor.mapDerivedCategoryFactors.hom.app P) =
          G.functor.mapDerivedCategoryFactors.hom.app
              ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) ≫
              ε'.app ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  let P := E.mapHomologicalComplex (.up ℤ)
  let ED := E.mapDerivedCategory
  let GD := G.mapDerivedCategory
  let eF : (L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙ GD.functor ≅
      P.functor ⋙ (L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    CategoryTheory.Functor.associator _ _ _ ≪≫
      CategoryTheory.Functor.isoWhiskerLeft _ G.functor.mapDerivedCategoryFactors ≪≫
        (CategoryTheory.Functor.associator _ _ _).symm ≪≫
          CategoryTheory.Functor.isoWhiskerRight
            (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (L ⋙ G.functor)) (.up ℤ) ≪≫
              NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
              (CategoryTheory.Functor.mapHomologicalComplexCompIso
                (Iso.refl (E.functor ⋙ L')) (.up ℤ)).symm) DerivedCategory.Q ≪≫
            CategoryTheory.Functor.associator _ _ _
  refine ⟨leftKanSquareIso P ED GD DerivedCategory.Q DerivedCategory.Q _ _ LF LF' ε ε'
    E.functor.mapDerivedCategoryFactors eF, ?_⟩
  intro X
  have h := NatTrans.congr_app
    (leftKanSquareIso_fac P ED GD DerivedCategory.Q DerivedCategory.Q _ _ LF LF' ε ε'
      E.functor.mapDerivedCategoryFactors eF) X
  have h' := congrArg (fun f ↦ f ≫ LF'.map
    (E.functor.mapDerivedCategoryFactors.hom.app X)) h
  simp only [leftKanSquareCounit, leftKanSquarePostCounit, eF, NatTrans.comp_app,
    CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.isoWhiskerRight_hom,
    Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_id,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Category.assoc, ← LF'.map_comp,
    Iso.inv_hom_id_app, LF'.map_id] at h'
  erw [Category.id_comp, Category.comp_id] at h'
  exact h'

/-- Data of compatible derived comparison squares, retaining the induced equivalences
and their localization factors as fields.
Source: Stacks Tags 05RR and 0941.
(blueprint: def-derived-exact-equivalence-square-data). -/
structure ExactEquivalenceDerivedSquareData
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (R : H ⥤ B) (R' : H' ⥤ B') [R.Additive] [R'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (RF : DerivedCategory H ⥤ DerivedCategory B)
    (RF' : DerivedCategory H' ⥤ DerivedCategory B')
    (ε : DerivedCategory.Q ⋙ LF ⟶
      L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ LF' ⟶
      L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (η' : R'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF')
    (eL : L ⋙ G.functor ≅ E.functor ⋙ L')
    (eR : R ⋙ E.functor ≅ G.functor ⋙ R') where
  equivalence : DerivedCategory B ≌ DerivedCategory B'
  towerEquivalence : DerivedCategory H ≌ DerivedCategory H'
  equivalenceIso : equivalence.functor ≅ E.mapDerivedCategory.functor
  localization : DerivedCategory.Q ⋙ equivalence.functor ≅
    E.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  towerLocalization : DerivedCategory.Q ⋙ towerEquivalence.functor ≅
    G.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  left : LF ⋙ towerEquivalence.functor ≅ equivalence.functor ⋙ LF'
  right : RF ⋙ equivalence.functor ≅ towerEquivalence.functor ⋙ RF'
  left_fac : ∀ P : CochainComplex B ℤ,
    left.hom.app (DerivedCategory.Q.obj P) ≫ LF'.map (localization.hom.app P) ≫
        ε'.app ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) =
      towerEquivalence.functor.map (ε.app P) ≫
        towerLocalization.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eL (.up ℤ)).hom.app P)
  right_fac : ∀ P : CochainComplex H ℤ,
    equivalence.functor.map (η.app P) ≫ right.hom.app (DerivedCategory.Q.obj P) ≫
        RF'.map (towerLocalization.hom.app P) =
      localization.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app P) ≫
          η'.app ((G.functor.mapHomologicalComplex (.up ℤ)).obj P)

/-- Exact equivalences carry a universal left-derived square and a universal
right-derived square to compatible natural isomorphisms on derived categories.

Source: Stacks Tags 05RR and 0941.
(blueprint: lem-derived-exact-equivalence-squares).

Proof: precomposition by an equivalence and postcomposition by an equivalence give
equivalences of the categories of Kan extensions. Transport the two universal pairs
through these equivalences and the ordinary comparison isomorphisms. Uniqueness of
universal extensions gives both derived isomorphisms. Their defining factorization
identities, evaluated on a complex and composed with the localization factorization,
are precisely the two equations below. -/
theorem exactEquivalenceDerivedSquares
    {B B' H H' : Type*} [Category* B] [Category* B']
    [Category* H] [Category* H'] [Abelian B] [Abelian B']
    [Abelian H] [Abelian H'] [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory H] [HasDerivedCategory H']
    (E : B ≌ B') (G : H ≌ H') [E.functor.Additive] [G.functor.Additive]
    (L : B ⥤ H) (L' : B' ⥤ H') [L.Additive] [L'.Additive]
    (R : H ⥤ B) (R' : H' ⥤ B') [R.Additive] [R'.Additive]
    (LF : DerivedCategory B ⥤ DerivedCategory H)
    (LF' : DerivedCategory B' ⥤ DerivedCategory H')
    (RF : DerivedCategory H ⥤ DerivedCategory B)
    (RF' : DerivedCategory H' ⥤ DerivedCategory B')
    (ε : DerivedCategory.Q ⋙ LF ⟶
      L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ LF' ⟶
      L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : R.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (η' : R'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF')
    [LF.IsRightKanExtension ε] [LF'.IsRightKanExtension ε']
    [RF.IsLeftKanExtension η] [RF'.IsLeftKanExtension η']
    (eL : L ⋙ G.functor ≅ E.functor ⋙ L')
    (eR : R ⋙ E.functor ≅ G.functor ⋙ R') :
    Nonempty (ExactEquivalenceDerivedSquareData E G L L' R R'
      LF LF' RF RF' ε ε' η η' eL eR) := by
  obtain ⟨φ, hφ⟩ := leftDerivedSquare E G L L' LF LF' ε ε' eL
  obtain ⟨ψ, hψ⟩ := rightDerivedSquare G E R R' RF RF' η η' eR
  exact ⟨{
    equivalence := E.mapDerivedCategory
    towerEquivalence := G.mapDerivedCategory
    equivalenceIso := Iso.refl _
    localization := E.functor.mapDerivedCategoryFactors
    towerLocalization := G.functor.mapDerivedCategoryFactors
    left := φ
    right := ψ
    left_fac := hφ
    right_fac := hψ }⟩

end CategoryTheory
