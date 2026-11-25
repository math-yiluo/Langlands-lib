/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
import WeilConjectures.AlgebraicGeometry.ProperShriekCompSupports
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Unit-coefficient diagonal forget-supports normalization

This is the coefficient-free special case used to prove the natural formula in
`SfDiagonalSectionForgetSupports` (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory

-- Normalize the constant comparison at the identity using its composition law.
private theorem constant_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z) (h : r = e ≫ p) :
    (upperStarComp (ModuleCat.{u + 1} A) e p r h).hom.app
        (ordinaryFiniteConstant A Z) ≫
      (upperStar (ModuleCat.{u + 1} A) e).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) p).hom.app
          (ModuleCat.of A A)) ≫
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) e).hom.app
        (ModuleCat.of A A) =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) r).hom.app
        (ModuleCat.of A A) := by
  subst r
  exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A) e p
    (ModuleCat.of A A)

private theorem constant_id (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (𝟙 X)).hom.app
        (ModuleCat.of A A) =
      (upperStarId (ModuleCat.{u + 1} A) X).hom.app (ordinaryFiniteConstant A X) := by
  let B := ModuleCat.{u + 1} A
  let c := (Scheme.upperStarConstantSheafIso B (𝟙 X)).hom.app (ModuleCat.of A A)
  have h := constant_comp A (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm
  have hu := upperStarComp_id_left B (𝟙 X)
  rw [hu] at h
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at h
  erw [Category.id_comp] at h
  have hc : IsIso c := by dsimp [c]; infer_instance
  change (upperStarId B X).inv.app ((upperStar B (𝟙 X)).obj
      (ordinaryFiniteConstant A X)) ≫ (upperStar B (𝟙 X)).map c ≫ c = c at h
  erw [← (upperStarId B X).inv.naturality_assoc c] at h
  have h' := (cancel_epi c).mp (h.trans (Category.comp_id c).symm)
  exact ((Iso.inv_comp_eq ((upperStarId B X).app (ordinaryFiniteConstant A X))).mp h').trans
    (Category.comp_id _)

-- The chosen derived identity comparison agrees with its levelwise construction.

private theorem exact_identity_fac
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Qh.obj K) =
      F.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at h
  dsimp at h
  simp only [Category.comp_id] at h
  erw [DerivedCategory.Qh.map_id] at h
  simp only [Category.comp_id] at h
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  erw [h, Functor.mapDerivedCategoryNatIso_fach]

private theorem right_identity_fac
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatIso e ≪≫
          (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightDerivedFunctorNatIso]
  rw [← Category.assoc]
  have h := NatTrans.congr_app
    (Functor.rightDerivedNatTrans_fac F.rightDerivedFunctor (𝟭 C).rightDerivedFunctor
      F.rightDerivedFunctorUnit (𝟭 C).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
        DerivedCategory.Qh)) K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  rw [Functor.rightDerivedFunctorNatTrans, h]
  simp only [Category.assoc]
  have hf := NatTrans.congr_app
    (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  erw [reassoc_of% hf]
  have hi := NatTrans.congr_app
    (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id] at hi
  dsimp at hi
  erw [DerivedCategory.Qh.map_id] at hi
  simp only [Category.comp_id] at hi
  erw [hi, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem factorsh_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
    F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    F.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj K))) = _
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id]
  change 𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) = _
  simp only [Category.id_comp, Category.comp_id]
  exact Category.comp_id _

private theorem exact_single_identity
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (M : C) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
      (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  let K := (CochainComplex.singleFunctor C 0).obj M
  let H := (HomotopyCategory.quotient C (.up ℤ)).obj K
  change _ = _
  rw [← cancel_epi (F.mapDerivedCategoryFactors.inv.app K)]
  have hi := exact_identity_fac F e H
  rw [factorsh_complex] at hi
  erw [hi, Iso.inv_hom_id_app_assoc]
  erw [← Category.assoc,
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  change DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (e.hom.app M))
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  ext n
  by_cases hn : n = 0
  · subst n
    simp [K, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex,
      CochainComplex.singleFunctor, HomologicalComplex.single]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_tgt

private theorem right_single_identity
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (M : C) :
    (Functor.rightDerivedFunctorNatIso e ≪≫
      (𝟭 C).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso C).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
      F.singleFunctorCompRightDerivedFunctorIso.hom.app M ≫
        (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  let H := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((CochainComplex.singleFunctor C 0).obj M)
  rw [← cancel_epi (F.rightDerivedFunctorUnit.app H)]
  erw [right_identity_fac]
  simp only [Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hf := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac H
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  erw [← Category.assoc, ← Category.assoc, hf, Category.assoc,
    ← exact_single_identity, exact_identity_fac, Iso.inv_hom_id_app_assoc]
  rfl

-- Exact single-object comparison reduces the remaining identity unit to sheaves.

private theorem supported_identity (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    supportedDerivedUnit A (𝟙 X) ≫
      (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
        (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app (ordinaryFiniteUnit A X) = 𝟙 _ := by
  erw [right_single_identity]
  rw [← Category.assoc]
  have h := Adjunction.derivedSingleUnit_comp_comparison
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
    (ordinaryFiniteConstant A X) (ordinaryFiniteConstant A X)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (𝟙 X)).hom.app
      (ModuleCat.of A A))
  have he : (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).homEquiv
      (ordinaryFiniteConstant A X) (ordinaryFiniteConstant A X)
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (𝟙 X)).hom.app
        (ModuleCat.of A A)) =
      (lowerStarId (ModuleCat.{u + 1} A) X).inv.app (ordinaryFiniteConstant A X) := by
    rw [constant_id, Adjunction.homEquiv_unit, upperStarId_hom_app_unit_app]
  rw [he] at h
  rw [show supportedDerivedUnit A (𝟙 X) ≫
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).singleFunctorCompRightDerivedFunctorIso.hom.app
        (ordinaryFiniteConstant A X) = _ from (by unfold supportedDerivedUnit; exact h)]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  exact CategoryTheory.Functor.map_id _ _

private theorem supported_comp_eq (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ Z) (r : X ⟶ Z) (h : e ≫ p = r) :
    supportedDerivedUnit A p ≫
        (ordinaryFinitePushforward A p).map (supportedDerivedUnit A e) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) e p r h).hom.app
          (ordinaryFiniteUnit A X) = supportedDerivedUnit A r := by
  subst r
  have hc : (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
      e p (e ≫ p) rfl).hom = (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e p).hom := by
    rw [rightDerivedLowerStarCompIsoOfComp, conjugateIsoEquiv_apply_hom,
      conjugateEquiv_leftDerivedUpperStarComp_hom]
    rfl
  rw [hc]
  exact supportedDerivedUnit_comp A e p

-- Cancel the compositor in the existing proper forget-supports compatibility.

private theorem cancel_proper_template
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ C} {E E' : C ⥤ D} {P P' : D ⥤ C}
    (ee : E ≅ E') (pp : P ≅ P')
    (i : F ≅ 𝟭 C) (e₀ : F ≅ G) (r : G ≅ 𝟭 C)
    (q : F ≅ E ⋙ P) (t : E' ⋙ P' ≅ G) (M : C)
    (hi : i = e₀ ≪≫ r)
    (hq : q.inv.app M ≫ e₀.hom.app M =
      P.map (ee.hom.app M) ≫ pp.hom.app (E'.obj M) ≫ t.hom.app M) :
    (i.symm ≪≫ q).hom.app M ≫ P.map (ee.hom.app M) ≫
      pp.hom.app (E'.obj M) ≫ t.hom.app M = r.inv.app M := by
  subst i
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Category.assoc]
  rw [← hq, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

attribute [local irreducible] rightDerivedLowerShriekIsoRightDerivedLowerStar

private theorem section_forget (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (e : X ⟶ Y) (p : Y ⟶ X) [IsProper e] [IsProper p]
    (h : e ≫ p = 𝟙 X) (M : DerivedCategoryModule A X) :
    ((rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).symm ≪≫
        properRouteCompIso A e p (𝟙 X) h).hom.app M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
        ((ordinaryProperForgetComparison A e).hom.app M) ≫
      (ordinaryProperForgetComparison A p).hom.app
        ((ordinaryFinitePushforward A e).obj M) ≫
      (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) e p (𝟙 X) h).hom.app M =
    (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
      (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _).inv.app M := by
  have hn := cancel_proper_template
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) e)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) p)
    (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 X))
    (Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
      (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (properRouteCompIso A e p (𝟙 X) h)
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) e p (𝟙 X) h)
    M rfl (properShriekComp_comp_forgetSupports A e p (𝟙 X) h M)
  -- Compare the aliases by congruence, keeping the canonical proper comparison folded.
  refine Eq.mp ?_ hn
  congr! (postTransparency := .reducible) <;> rfl

private theorem shriek_congr_symm (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {g g' : X ⟶ Y}
    [HasCompactification g] [HasCompactification g'] (h : g = g') :
    rightDerivedLowerShriekCongrIso A h.symm = (rightDerivedLowerShriekCongrIso A h).symm := by
  subst g'
  rfl

attribute [local semireducible] projection

private theorem diagonalUnit_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (a : Bool)
    (h : TraceDiagonalDatum.diagonal f ≫ projection f a = 𝟙 X) :
    diagonalUnit A f a =
      ((rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).symm ≪≫
        properRouteCompIso A (TraceDiagonalDatum.diagonal f) (projection f a) (𝟙 X) h).hom.app
          (derivedTensorUnit (ModuleCat.{u + 1} A) X) := by
  cases a
  · unfold diagonalUnit projection
    dsimp only
    unfold SfDiagonalKernel.diagonalFirst properRouteCompIso
    erw [← shriek_congr_symm]
    rfl
  · unfold diagonalUnit projection
    dsimp only
    unfold TraceDiagonalDatum.idIsoDiagonalSnd properRouteCompIso
    erw [← shriek_congr_symm]
    rfl

private theorem conjugate_identity
    {C : Type*} [Category C] {F : C ⥤ C} (r : F ≅ 𝟭 C) {M N : C} (c : M ≅ N) :
    r.inv.app N = c.inv ≫ r.inv.app M ≫ F.map c.hom := by
  have h := congrArg (fun z ↦ c.inv ≫ z) (r.inv.naturality c.hom)
  simpa only [Functor.id_map, Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The diagonal section normalization for the tensor unit and its identity map.

Source: blueprint latest, `thm-amb-p1-adjunction.proof.md`, the equation
`M = Rp₂_* Δ_* M` for the constant object.  Expand the selected compact-support
compositor for `Δ` followed by either projection, apply the canonical proper
forget-supports comparisons, and use the composition-unit identity for the
ordinary direct-image adjunction.  The two Boolean cases use `diagonal_fst` and
`diagonal_snd`; this is the coefficient-free core of the natural statement.
(auxiliary; not a blueprint node). -/
theorem diagonalSection_forgetSupports_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] (a : Bool) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          ((ordinaryProperForgetComparison A
              (TraceDiagonalDatum.diagonal f)).hom.app
                (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
            (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
              (𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))) ≫
        (ordinaryProperForgetComparison A
          (projection f a)).hom.app
            ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).obj
              (derivedTensorUnit (ModuleCat.{u + 1} A) X)) =
      (constantUnit A X).inv ≫ supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            ((constantUnit A X).hom ≫
              𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))) := by
  have h : TraceDiagonalDatum.diagonal f ≫ projection f a = 𝟙 X := by
    cases a <;> simp only [projection]
    · exact TraceDiagonalDatum.diagonal_fst f
    · exact TraceDiagonalDatum.diagonal_snd f
  let c := constantUnit A X
  let q := rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
    (TraceDiagonalDatum.diagonal f) (projection f a) (𝟙 X) h
  let r := Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  rw [← cancel_mono (q.hom.app (derivedTensorUnit (ModuleCat.{u + 1} A) X))]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
  rw [diagonalUnit_eq A f a h, section_forget A _ _ h]
  have hn := q.hom.naturality c.hom
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  have hi := supported_identity A X
  have hu : supportedDerivedUnit A (𝟙 X) = r.inv.app (ordinaryFiniteUnit A X) := by
    apply (cancel_mono (r.hom.app _)).mp
    exact hi.trans (Iso.inv_hom_id_app r _).symm
  have hcomp := supported_comp_eq A (TraceDiagonalDatum.diagonal f)
    (projection f a) (𝟙 X) h
  have he := congrArg (fun z ↦ c.inv ≫ z ≫
    (ordinaryFinitePushforward A (𝟙 X)).map c.hom) hcomp
  simp only [Category.assoc] at he
  erw [he, hu]
  exact conjugate_identity r c

end AlgebraicGeometry.Etale.SfP1Transport
