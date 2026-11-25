/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Open.OpenSourceComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

set_option linter.privateModule false
/-! The compactification tower calculation for open composition. -/
@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Etale
universe u
set_option autoImplicit false
open CategoryTheory.Abelian
universe v u₁ u₂
private theorem derived_comp_right_unit
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : G ≅ 𝟭 D) :
    (Functor.rightDerivedFunctorCompIso' F G
      (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).hom =
      Functor.whiskerLeft F.rightDerivedFunctor
        (G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom ≫
        (Functor.rightUnitor F.rightDerivedFunctor).hom := by
  apply (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerived_ext
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ))
  ext K
  have hL : (Functor.rightDerivedFunctorCompUnit F G).app K ≫
      (Functor.rightDerivedFunctorCompIso' F G
        (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).hom.app
          (DerivedCategory.Qh.obj K) =
      (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans
          (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F).hom).app
          (DerivedCategory.Qh.obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [hL]
  simp only [Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app,
    Functor.whiskerRight_app]
  let ei := G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D
  change _ = (Functor.rightDerivedFunctorCompUnit F G).app K ≫
    ei.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫ 𝟙 _
  rw [Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [ei.hom.naturality (F.rightDerivedFunctorUnit.app K)]
  simp only [Functor.id_map]
  simp only [ei, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have hq := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hq
  erw [reassoc_of% hq]
  erw [Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc
    e ((F.mapHomotopyCategory (.up ℤ)).obj K)]
  erw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  congr 1
  have hc := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).hom_inv_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hc
  rw [hc]
  erw [Category.id_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  congr 1
  ext n
  exact Category.comp_id _
private theorem direct_image_right_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f (𝟙 Y)).hom =
      Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (rightDerivedLowerStarIdIso A Y).hom ≫ (Functor.rightUnitor _).hom := by
  let B := ModuleCat.{u + 1} A
  have hc := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B (𝟙 Y))
    (upperStarLowerStarAdjunction B (f ≫ 𝟙 Y)) (lowerStarComp B f (𝟙 Y))
    (upperStarComp B f (𝟙 Y))
    (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp B f (𝟙 Y))).symm
  have hh : (rightDerivedLowerStarComp B f (𝟙 Y)).hom =
      (Functor.rightDerivedFunctorCompIso' (lowerStar B f) (lowerStar B (𝟙 Y))
        (lowerStarComp B f (𝟙 Y))).hom := hc.symm
  rw [hh]
  have he : lowerStarComp B f (𝟙 Y) =
      Functor.isoWhiskerLeft (lowerStar B f) (lowerStarId B Y) ≪≫
        Functor.rightUnitor (lowerStar B f) := lowerStarComp_id_right B f
  rw [he]
  exact derived_comp_right_unit (lowerStar B f) (lowerStar B (𝟙 Y)) (lowerStarId B Y)
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] CategoryTheory.Abelian.toPreadditive
attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  rightDerivedLowerShriekIso rightDerivedLowerShriekOfCompactificationIso
  unboundedEtaleLowerShriekCompIso openImmersionLowerShriekLowerStarExchange
private theorem congr_symm (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    (unboundedEtaleLowerShriekCongr A h).inv =
      (unboundedEtaleLowerShriekCongr A h.symm).hom := by
  cases h
  rfl
private theorem open_congr_derived (A : Type (u + 1)) [CommRing A]
    {W Z : Scheme.{u}} {i j : W ⟶ Z}
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h =
      Functor.mapDerivedCategoryNatIso (eqToIso (by congr 1)) := by
  cases h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl.symm
end AlgebraicGeometry.Etale
