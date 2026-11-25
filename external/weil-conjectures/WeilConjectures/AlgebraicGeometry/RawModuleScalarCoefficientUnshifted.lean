/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceSquareCore
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSheafComposition

/-! Unshifted coefficient identity used by the shifted scalar square.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-unshifted). -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor

private theorem plusCompatibility_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  change NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
      (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
  infer_instance

private theorem plusNatIso_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e).hom ≫
          G.mapDerivedCategoryPlusCompatibility.inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

private theorem plusCompIso_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι =
      (F ⋙ G).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).inv ≫
        (associator _ _ _).inv ≫
        whiskerRight F.mapDerivedCategoryPlusCompatibility.inv G.mapDerivedCategory ≫
        (associator _ _ _).hom ≫
        whiskerLeft F.mapDerivedCategoryPlus G.mapDerivedCategoryPlusCompatibility.inv ≫
        (associator _ _ _).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app]
    rw [ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Functor.map_id]
    repeat erw [Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    have := plusCompatibility_commShift (F ⋙ G)
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

private theorem plusNatIso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    mapDerivedCategoryPlusNatIso e.symm = (mapDerivedCategoryPlusNatIso e).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [mapDerivedCategoryPlusNatIso, fullyFaithfulCancelRight_hom_app,
    fullyFaithfulCancelRight_inv_app, Iso.symm_hom, Iso.symm_inv,
    Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

namespace RawModuleScalarComparison



end RawModuleScalarComparison

/-- The derived scalar pullback comparison commutes with integer shifts.
Source: Stacks Project, Tags 03D7 and 03Q8. Expand the defining composite
into its three comparison isomorphisms and apply `NatTrans.shift_app_comm`
to each factor; compatibility of composition and associativity then give
the inverse composite's `CommShift` instance for every integer shift.
(blueprint: lem-sbc-raw-scalar-derived-pullback-shift) -/
theorem rawModuleScalar_derivedPullbackIso_commShift
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (moduleAbelianDerivedUpperStarIso Λ f).hom ℤ := by
  let : PreservesFiniteLimits
      (upperStar (ModuleCat.{u + 1} Λ) f ⋙ moduleAbelianForget Λ X) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits
      (upperStar (ModuleCat.{u + 1} Λ) f ⋙ moduleAbelianForget Λ X) :=
    comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits
      (moduleAbelianForget Λ Y ⋙ upperStar AddCommGrpCat.{u + 1} f) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits
      (moduleAbelianForget Λ Y ⋙ upperStar AddCommGrpCat.{u + 1} f) :=
    comp_preservesFiniteColimits _ _
  have := Functor.plusCompIso_commShift
    (upperStar (ModuleCat.{u + 1} Λ) f) (moduleAbelianForget Λ X)
  have := Functor.plusNatIso_commShift (moduleAbelianUpperStarIso Λ f)
  have := Functor.plusCompIso_commShift
    (moduleAbelianForget Λ Y) (upperStar AddCommGrpCat.{u + 1} f)
  unfold moduleAbelianDerivedUpperStarIso
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The unshifted coefficient-factor square follows by inverting the source-factor square
at the identity coefficient map and cancelling the derived scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8. Specialize the source square to
the coefficient sheaf and identity map, use invertibility of its source
factors, and rewrite with `Functor.map_inv` and associativity. Cancellation
of the derived scalar comparison yields the displayed equality. This applies
to identity arrows, zero coefficients, and arbitrary schemes in the stated
universes.
(blueprint: lem-sbc-raw-scalar-coefficient-unshifted) -/
theorem rawModuleScalar_coefficient_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (A B : Over W) (f : A ⟶ B) :
    (moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor
          0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
            (Over.w f).symm).inv.app G)) ≫
      ((moduleAbelianForget Λ A.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)) =
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
      (((moduleAbelianForget Λ B.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ B.hom G))) ≫
      ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor
        0).hom.app _ ≫ (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app _) := by
  let M := upperStar (ModuleCat.{u + 1} Λ) f.left
  let V' := moduleAbelianForget Λ A.left
  let V := moduleAbelianForget Λ B.left
  let H := upperStar AddCommGrpCat.{u + 1} f.left
  let e := RawModuleScalarComparison.pullbackIso Λ f.left
  let m := (upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
    (Over.w f).symm).hom.app G
  let k := (upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
    (Over.w f).symm).hom.app ((moduleAbelianForget Λ W).obj G)
  let cA := RawModuleScalarComparison.pullback Λ A.hom G
  let cB := RawModuleScalarComparison.pullback Λ B.hom G
  have hs := Functor.plus_single_source_square_core M V' V H e 0 m k cA cB
    (rawModuleScalar_sheaf_composition Λ f.left B.hom A.hom (Over.w f) G)
  have hi := IsIso.inv_eq_inv.mpr hs
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_inv_app] at hi
  have hi' := congrArg
    (fun z ↦ (moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)) ≫ z) hi
  simpa only [moduleAbelianDerivedUpperStarIso, RawModuleScalarComparison.pullbackIso,
    Functor.plusNatIso_symm, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, M, V', V, H, e,
    m, k, cA, cB, Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.id_comp, NatIso.inv_hom_app] using hi'

end AlgebraicGeometry.Etale
