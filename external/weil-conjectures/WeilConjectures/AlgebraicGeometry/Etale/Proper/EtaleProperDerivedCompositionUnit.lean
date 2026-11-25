/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Unit normalization for inverse derived direct-image composition -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedEtaleLowerShriekUpperStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction
  upperStarLowerStarAdjunction Adjunction.mapDerivedCategoryAdjunction

private lemma comp_homotopy_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma right_comp_inv_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (J : HomotopyCategory C (.up ℤ)) :
    H.rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompIso' F G e).inv.app (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app J ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app J) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj J) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app J) := by
  simp only [comp_homotopy_inv, Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app]
  rw [← Category.assoc]
  erw [Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ J]
  rw [Category.assoc, right_comp_unit]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, comp_homotopy_inv, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id]
  all_goals erw [Category.id_comp]

/-- The inverse proper direct-image compositor carries the unit to the two
successive right-derived units and the inverse ordinary compositor.
Source: Stacks Project Tag 0F7B; the ordinary derived-composition unit identity.
(blueprint: lem-pur-proper-derived-composition-unit). -/
theorem properDerivedComposition_inv_unit
    (A : Type (u + 1)) [CommRing A]
    {W Z V : Scheme.{u}} (a : W ⟶ Z) (b : Z ⟶ V) (d : W ⟶ V) (w : a ≫ b = d)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (lowerStar (ModuleCat.{u + 1} A) d).rightDerivedFunctorUnit.app J ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a b d w).inv.app
        (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (lowerStarComp (ModuleCat.{u + 1} A) a b d w.symm).inv (.up ℤ)).app J ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (lowerStar (ModuleCat.{u + 1} A) a ⋙ lowerStar (ModuleCat.{u + 1} A) b))
          (.up ℤ)).inv.app J) ≫
      (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctorUnit.app
        ((lowerStar (ModuleCat.{u + 1} A) a).mapHomotopyCategory (.up ℤ) |>.obj J) ≫
      (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorUnit.app J) := by
  subst d
  let B := ModuleCat.{u + 1} A
  let F := lowerStar B a
  let G := lowerStar B b
  let H := lowerStar B (a ≫ b)
  let e := lowerStarComp B a b
  have hi : (rightDerivedLowerStarComp B a b).inv =
      (Functor.rightDerivedFunctorCompIso' F G e).inv :=
    congrArg Iso.inv (Iso.ext (right_derived_star_comp_eq A a b)).symm
  change H.rightDerivedFunctorUnit.app J ≫
    (rightDerivedLowerStarComp B a b).inv.app (DerivedCategory.Qh.obj J) = _
  rw [hi]
  exact right_comp_inv_unit F G H e J

end AlgebraicGeometry.Etale
