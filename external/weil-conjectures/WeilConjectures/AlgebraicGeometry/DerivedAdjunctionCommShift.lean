/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-!
# Shift compatibility of the bounded below derived étale adjunction

Source: Stacks Project, Derived Categories, Tags 0A8D, 0DVC and 05SU;
(blueprint: lem-weil-pbc-derived-adjunction-commshift).

The shift structures are the existing termwise structure on `mapDerivedCategoryPlus` and
resolution-comparison structure on `rightDerivedFunctorPlus`, not structures transported
from an abstract adjunction. `Adjunction.CommShift ℤ` asserts compatibility of both the
unit and counit, including all iterated integer shifts.
-/

@[expose] public section

universe u

open CategoryTheory

-- The bounded below inclusion is faithful and its lift comparison isos commute with shifts.
private theorem plusHomotopyUnit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R) :
    NatTrans.CommShift adj.mapHomotopyCategoryPlus.unit ℤ := by
  have heq : Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit
      (HomotopyCategory.Plus.ι C) =
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (adj.mapHomotopyCategory (.up ℤ)).unit ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ((HomotopyCategory.plus D).liftCompιIso _ _).inv
          (R.mapHomotopyCategory (.up ℤ)) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus
          ((HomotopyCategory.plus C).liftCompιIso _ _).inv ≫
        (Functor.associator _ _ _).inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      ObjectProperty.liftCompιIso, Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.comp_id, Category.comp_id, Category.comp_id]
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
    simp only [Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit
      (HomotopyCategory.Plus.ι C)) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι C)

-- Compute the derived unit on the localization image, then use essential surjectivity.
private theorem derivedUnit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L] (adj : L ⊣ R) :
    NatTrans.CommShift adj.derivedPlus.unit ℤ := by
  have := plusHomotopyUnit_commShift adj
  have heq : Functor.whiskerLeft DerivedCategory.Plus.Qh adj.derivedPlus.unit =
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight adj.mapHomotopyCategoryPlus.unit DerivedCategory.Plus.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnith ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom := by
    refine NatTrans.ext (funext fun K ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp]
    simp only [Category.comp_id]
    rw [← cancel_mono (R.rightDerivedFunctorPlus.map
      (L.mapDerivedCategoryPlusFactorsh.hom.app K)),
      Adjunction.derivedPlus_unit_app_fac]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Plus.Qh adj.derivedPlus.unit) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh
    (fun X ↦ ⟨DerivedCategory.Plus.Qh.objPreimage X,
      (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩)

namespace AlgebraicGeometry.Etale

/-- The unit and counit of `u⁻¹ ⊣ Ru_*` on bounded below derived categories of abelian
étale sheaves commute with the specified shift isomorphisms, for every integer shift.
Source: Stacks Project, Tags 0A8D, 0DVC and 05SU;
(blueprint: lem-weil-pbc-derived-adjunction-commshift).

Proof plan from the node:
1. Compare K-injective resolutions using the unique homotopy classes of comparisons
   (`lem-weil-pbc-kinjective-hom-derived`). Shifting a resolution remains a resolution
   (`lem-weil-pbc-kinjective-shift`). The comparison shift isomorphism on a K-injective
   representative is the termwise identity, after the resolution identifications.
2. Compute the counit on a K-injective representative by the termwise sheaf counit
   (`prose-04-06`). Its components commute with shift;
   combine with step 1 and naturality of the inverse-image shift isomorphism.
3. Transport the counit equality along a K-injective representative isomorphism by
   naturality (`lem-weil-pbc-dplus-injective-representative`).
4. Compute the unit on a bounded below complex by the termwise unit followed by the
   direct image of its inverse-image resolution. Shift the resolution and use uniqueness
   of comparisons to obtain the unit equality.
5. Transport the unit equality to every derived object using a bounded below
   representative and naturality (`lem-weil-pbc-dplus-injective-representative`).
6. The composite shift structures are the whiskered composites
   (`lem-weil-pbc-triangulated-functor-composite`,
   `lem-weil-pbc-commshift-nattrans-comp-whisker`). Induct for positive shifts, use inverses
   for negative shifts, and use the identity for zero.
7. The unit equality identifies the resolution-comparison structure with the unique
   adjunction-induced structure (`lem-weil-pbc-adjunction-shift-compatibility-unique`). -/
theorem derivedPlus_upperStarLowerStar_commShift {U V : Scheme.{u}} (f : U ⟶ V) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus).CommShift ℤ := by
  have := derivedUnit_commShift (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact Adjunction.CommShift.mk' _ ℤ (by infer_instance)

end AlgebraicGeometry.Etale
