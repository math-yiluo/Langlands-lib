/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphCompactificationUnit
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperPrecompositionUnit
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperPostcomposition
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Proper-support tower normalization through the right-derived unit

Source: Stacks Project, Tags 0F7B, 0F7F, 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [local irreducible] canonicalEtaleCompactSupportComparison
  derivedEtaleLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

section UnitCalculus

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions E]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions E] in
private lemma comp_homotopy_inv (R : C ⥤ D) (P : D ⥤ E)
    [R.Additive] [P.Additive] (J : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).inv.app J =
      𝟙 _ := by
  have h := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (R ⋙ P)) (.up ℤ)).hom_inv_id_app J
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

omit [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions E] in
private lemma exact_left_unit_app (O : C ⥤ D) (R : D ⥤ E)
    [O.Additive] [R.Additive] [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O R).app J =
      R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj J) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app J) := by
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, comp_homotopy_inv,
    DerivedCategory.Qh.map_id, Category.id_comp]

private lemma proper_comp_unit (R : D ⥤ E) (P : E ⥤ F) (T : D ⥤ F)
    [R.Additive] [P.Additive] [T.Additive] [R.PreservesKInjectiveComplexes]
    (κ : R ⋙ P ≅ T) (J : HomotopyCategory D (.up ℤ)) :
    P.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj J) ≫
        P.rightDerivedFunctor.map (R.rightDerivedFunctorUnit.app J) ≫
        (Functor.rightDerivedFunctorCompIso' R P κ).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ.hom (.up ℤ)).app J) ≫
        T.rightDerivedFunctorUnit.app J := by
  have hc := right_comp_unit R P J
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, comp_homotopy_inv, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id] at hc
  rw [← reassoc_of% hc]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
  exact Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso D (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory κ.hom (.up ℤ)) DerivedCategory.Qh) J

omit [Abelian.HasKInjectiveResolutions C] in
private lemma postcomposition_unit
    (S : C ⥤ D) (O : C ⥤ E) (R : E ⥤ D) (P : D ⥤ F) (T : E ⥤ F)
    [S.Additive] [O.Additive] [R.Additive] [P.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [R.PreservesKInjectiveComplexes]
    (a : S ⟶ O ⋙ R) (κ : R ⋙ P ≅ T)
    (γ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (hγ : ∀ J : HomotopyCategory C (.up ℤ),
      γ.app (DerivedCategory.Qh.obj J) =
        S.mapDerivedCategoryFactorsh.hom.app J ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a (.up ℤ)).app J) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O R).app J)
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit S P).app J ≫
        P.rightDerivedFunctor.map (γ.app (DerivedCategory.Qh.obj J)) ≫
        (Functor.rightDerivedFunctorCompIso' R P κ).hom.app
          (O.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (Functor.whiskerRight a P ≫ (Functor.associator O R P).hom ≫
          Functor.whiskerLeft O κ.hom) (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O T).app J := by
  rw [hγ]
  simp only [exact_left_unit_app, Functor.map_comp, Category.assoc]
  rw [← P.rightDerivedFunctor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [P.rightDerivedFunctor.map_id, Category.id_comp]
  erw [← P.rightDerivedFunctorUnit.naturality_assoc]
  erw [(Functor.rightDerivedFunctorCompIso' R P κ).hom.naturality]
  simp only [Functor.comp_map]
  erw [reassoc_of% (proper_comp_unit R P T κ
    ((O.mapHomotopyCategory (.up ℤ)).obj J))]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  change (HomotopyCategory.quotient F (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient F (.up ℤ)).map _ =
    (HomotopyCategory.quotient F (.up ℤ)).map _
  rw [← (HomotopyCategory.quotient F (.up ℤ)).map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Functor.mapHomologicalComplex_map_f]
  rfl

end UnitCalculus

private theorem cancel_whisker_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) {F G : D ⥤ E} (e : F ≅ G)
    {H : C ⥤ E} {a b : H ⟶ Q ⋙ F} :
    a ≫ Functor.whiskerLeft Q e.hom = b ≫ Functor.whiskerLeft Q e.hom → a = b :=
  (Iso.cancel_iso_hom_right a b (Functor.isoWhiskerLeft Q e)).1

private lemma postcomp_sheaf_normalization
    (A : Type (u + 1)) [CommRing A]
    {W Z Y : Scheme.{u}} (b : W ⟶ Z) [Etale b] [IsSeparated b]
    (c : Compactification b) (p : Z ⟶ Y) [IsProper p]
    (M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) p).map
        ((etaleCompactificationGraphMap A b c).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) c.g p).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
      (compactificationSheafToDirectImage A (c.postcomp p)).app M =
    (lowerStar (ModuleCat.{u + 1} A) p).map
        (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) b p).hom.app M := by
  let B := ModuleCat.{u + 1} A
  have hc := congr_app (lowerStarComp_assoc' B c.i c.g p b (c.g ≫ p) (b ≫ p)
    c.comm rfl rfl) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hc
  dsimp only [compactificationSheafToDirectImage, Compactification.postcomp,
    NatTrans.comp_app, Functor.whiskerRight_app]
  rw [← (lowerStarComp B c.g p).hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← hc]
  simp only [← Functor.map_comp_assoc]
  erw [← (lowerStar B p).map_comp_assoc]
  change (lowerStar B p).map
    ((etaleCompactificationGraphMap A b c).app M ≫
      (compactificationSheafToDirectImage A c).app M) ≫ _ = _
  rw [compactSupportGraphSheafComparison_normalization]

private lemma postcomp_word
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian Z] [IsNoetherian Y]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    [HasCompactification b] (c : Compactification b)
    (hc : c = HasCompactification.compactification b)
    (p : Z ⟶ Y) [IsProper p] [HasCompactification (b ≫ p)]
    (K : DerivedCategoryModule A W) :
    (graphChosenProperComparison A p).inv.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
        ((graphChosenEtaleComparison A b).inv.app K) ≫
      (unboundedEtaleLowerShriekCompIso A b p).hom.app K =
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map
        ((canonicalEtaleCompactSupportComparison A b c).inv.app K) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) c.g p).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriekIso A (c.postcomp p)).hom.app K := by
  have hd : (graphChosenEtaleComparison A b).inv.app K =
      (canonicalEtaleCompactSupportComparison A b c).inv.app K ≫
        (rightDerivedLowerShriekIso A c).hom.app K := by
    subst c
    unfold graphChosenEtaleComparison
    rfl
  rw [hd, Functor.map_comp]
  simp only [Category.assoc]
  erw [← (graphChosenProperComparison A p).inv.naturality_assoc]
  have hp := congrArg (fun e ↦ e.hom.app K) (graph_proper_postcomposition A c p)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at hp
  dsimp only [rightDerivedLowerStar, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj] at hp
  simp only [Category.id_comp, Category.assoc] at hp
  erw [hp]
  simp only [rightDerivedLowerStar, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Iso.inv_hom_id_app_assoc]

section PostModel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {W Z Y : Scheme.{u}} [IsNoetherian W] [IsNoetherian Z] [IsNoetherian Y]
  (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
  [HasCompactification b] (c : Compactification b)
  (p : Z ⟶ Y) [IsProper p] [HasCompactification (b ≫ p)]

@[irreducible] private noncomputable def post_word :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) (b ≫ p) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerStar (ModuleCat.{u + 1} A) p :=
  (unboundedEtaleLowerShriekCompIso A b p).symm ≪≫
    Functor.isoWhiskerRight (graphChosenEtaleComparison A b)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
    Functor.isoWhiskerLeft
      (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory
      (graphChosenProperComparison A p)

@[irreducible] private noncomputable def post_model :
    (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerStar (ModuleCat.{u + 1} A) p ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (c.postcomp p) :=
  (post_word A b p).symm ≪≫ (rightDerivedLowerShriekIso A (c.postcomp p)).symm

private lemma post_model_app
    (hc : c = HasCompactification.compactification b) (K : DerivedCategoryModule A W) :
    (post_model A b c p).hom.app K =
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((canonicalEtaleCompactSupportComparison A b c).inv.app K) ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} A) c.g) (lowerStar (ModuleCat.{u + 1} A) p)
        (lowerStarComp (ModuleCat.{u + 1} A) c.g p)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) := by
  dsimp only [rightDerivedLowerStar, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Compactification.postcomp]
  unfold post_model post_word
  dsimp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [reassoc_of% (postcomp_word A b c hc p K)]
  simp only [Iso.hom_inv_id_app]
  rw [right_derived_star_comp_eq]
  simp only [rightDerivedLowerStar, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Compactification.postcomp, Category.comp_id]

end PostModel

private theorem graph_proper_support_unit_aux
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Y' Z Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian Y'] [IsNoetherian Z] [IsNoetherian Y]
    (q : W ⟶ Y') [IsProper q] (p : Z ⟶ Y) [IsProper p]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (sq : CommSq b q p v)
    [HasCompactification b] [HasCompactification v]
    [HasCompactification (q ≫ v)] [HasCompactification (b ≫ p)]
    (c : Compactification b)
    (hchosen : c = HasCompactification.compactification b)
    (θ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance ⋙
        lowerStar (ModuleCat.{u + 1} A) p)
    (hθ : (∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      θ.app F ≫
          (lowerStar (ModuleCat.{u + 1} A) p).map
            (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) b p).hom.app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v (b ≫ p) sq.w).hom.app F)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
      (lowerStar (ModuleCat.{u + 1} A) q)
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance)) ≫
      Functor.whiskerLeft DerivedCategory.Qh
    (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
        (graphChosenEtaleComparison A v).symm ≪≫
      unboundedEtaleLowerShriekCompIso A q v ≪≫
      unboundedEtaleLowerShriekCongr A sq.w.symm ≪≫
      (unboundedEtaleLowerShriekCompIso A b p).symm ≪≫
      Functor.isoWhiskerRight (graphChosenEtaleComparison A b)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory
        (graphChosenProperComparison A p)).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory θ (.up ℤ)) DerivedCategory.Qh ≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance)
        (lowerStar (ModuleCat.{u + 1} A) p) := by
  let S := etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance
  let O := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let R := lowerStar (ModuleCat.{u + 1} A) c.g
  let P := lowerStar (ModuleCat.{u + 1} A) p
  let T := lowerStar (ModuleCat.{u + 1} A) (c.g ≫ p)
  let a := etaleCompactificationGraphMap A b c
  let κ := lowerStarComp (ModuleCat.{u + 1} A) c.g p
  let η : S ⋙ P ⟶ O ⋙ T :=
    Functor.whiskerRight a P ≫ (Functor.associator O R P).hom ≫
      Functor.whiskerLeft O κ.hom
  let τ := θ ≫ η
  have hτ (M) : τ.app M ≫
      (compactificationSheafToDirectImage A (c.postcomp p)).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) q v (b ≫ p) sq.w).hom.app M := by
    dsimp only [τ, η, P, a, κ, O, R, T, Compactification.postcomp,
      NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app]
    simp only [Category.id_comp, Category.assoc]
    erw [postcomp_sheaf_normalization A b c p M]
    exact hθ M
  let pre :=
    Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
        (graphChosenEtaleComparison A v).symm ≪≫
      unboundedEtaleLowerShriekCompIso A q v ≪≫
      unboundedEtaleLowerShriekCongr A sq.w.symm
  let post := post_word A b p
  let e := post_model A b c p
  have he := post_model_app A b c p hchosen
  have hγ := graph_compactification_unit A b c
  have hpost : Functor.mapDerivedCategoryCompRightDerivedFunctorUnit S P ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory η (.up ℤ)) DerivedCategory.Qh ≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O T := by
    apply NatTrans.ext
    funext J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, e, he]
    exact postcomposition_unit S O R P T a κ
      (canonicalEtaleCompactSupportComparison A b c).inv hγ J
  have hpre := graph_proper_precomposition_unit A q v sq.w (c.postcomp p) τ hτ
  have hβ : Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (c.postcomp p).i)
      (lowerStar (ModuleCat.{u + 1} A) (c.postcomp p).g) =
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O T := rfl
  rw [hβ] at hpre
  apply cancel_whisker_iso DerivedCategory.Qh e
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  have hc : (pre ≪≫ post).hom ≫ e.hom =
      (pre ≪≫ (rightDerivedLowerShriekIso A (c.postcomp p)).symm).hom := by
    simp only [e, post_model, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change pre.hom ≫ post.hom ≫ post.inv ≫ _ = _
    rw [← Category.assoc post.hom, Iso.hom_inv_id, Category.id_comp]
  simp only [pre, post, post_word, Iso.trans_hom, Category.assoc] at hc
  simp only [Iso.trans_hom, Category.assoc]
  rw [hc]
  erw [hpost]
  simpa only [Iso.trans_hom,
    Functor.whiskerLeft_comp, τ,
    NatTrans.mapHomotopyCategory_comp, Functor.whiskerRight_comp, Category.assoc] using hpre

/-- A sheaf map normalized in the common ordinary direct image computes the
compact-support tower interchange after the source right-derived unit.
Source: Stacks Project, Tags 0F7B, 0F7F, 0F7I and 0F7J
(blueprint: lem-pur-graph-proper-support-unit).

Proof in words: use the chosen compactification c of b and postcompose it by p.
Compose theta with the sheaf graph map for b and then the ordinary direct-image
compositor for c.g and p, obtaining tau with target the sheaf model of c.postcomp p.
Naturality of the direct-image compositor, its associativity equation, graph sheaf
normalization and htheta prove that tau has the required normalization into (b followed
by p)_*. Apply graph_proper_precomposition_unit to q, v, and this single model.
For the other path, graph_proper_postcomposition identifies the chosen compositor
with composition of the two proper direct images. The defining homotopy formula of
the graph-derived comparison and the unit equation of proper direct-image composition
show that the unit for D(b_!) followed by Rp_* becomes degreewise tau followed by the
model's unit. This calculation uses naturality of the right-derived unit twice, then
cancels the exact-functor factor and the inverse composition isomorphism. Postcompose
both sides with the inverse of the terminal compactification word and the model
comparison. The two established unit equations agree there; cancel this isomorphism.
The calculation is on arbitrary homotopy objects and uses no boundedness or Cartesian
hypothesis. No noncanonical functor or resolution is chosen in this reduction. -/
theorem graph_proper_support_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Y' Z Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian Y'] [IsNoetherian Z] [IsNoetherian Y]
    (q : W ⟶ Y') [IsProper q] (p : Z ⟶ Y) [IsProper p]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (sq : CommSq b q p v)
    [HasCompactification b] [HasCompactification v]
    [HasCompactification (q ≫ v)] [HasCompactification (b ≫ p)]
    (θ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance ⋙
        lowerStar (ModuleCat.{u + 1} A) p)
    (hθ : (∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      θ.app F ≫
          (lowerStar (ModuleCat.{u + 1} A) p).map
            (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) b F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) b p).hom.app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v (b ≫ p) sq.w).hom.app F)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
      (lowerStar (ModuleCat.{u + 1} A) q)
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance)) ≫
      Functor.whiskerLeft DerivedCategory.Qh
    (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
        (graphChosenEtaleComparison A v).symm ≪≫
      unboundedEtaleLowerShriekCompIso A q v ≪≫
      unboundedEtaleLowerShriekCongr A sq.w.symm ≪≫
      (unboundedEtaleLowerShriekCompIso A b p).symm ≪≫
      Functor.isoWhiskerRight (graphChosenEtaleComparison A b)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory
        (graphChosenProperComparison A p)).hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory θ (.up ℤ)) DerivedCategory.Qh ≫
      Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance)
        (lowerStar (ModuleCat.{u + 1} A) p) := by
  exact graph_proper_support_unit_aux A q p b v sq
    (HasCompactification.compactification b) rfl θ hθ

end AlgebraicGeometry.Etale
