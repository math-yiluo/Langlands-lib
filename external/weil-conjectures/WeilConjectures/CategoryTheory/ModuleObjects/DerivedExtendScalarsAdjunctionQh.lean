/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!
# The derived extension–restriction adjunction on complexes

Let `φ : R ⟶ S` be a morphism of commutative algebra objects. The unit and the counit of the
derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` (`Mod.derivedExtendMapDerivedCategoryAdjunction`) on
the image of a complex are the levelwise unit and counit, read through the counit of the derived
extension of scalars (`Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh`,
`Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh`).
-/

@[expose] public section

universe v u'

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u'} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The counit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `M`
is the levelwise counit, read through the counit of the derived extension of scalars. -/
lemma derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh
    (M : HomotopyCategory (Mod C S) (ComplexShape.up ℤ)) :
    (extendScalars φ).leftDerivedFunctor.map
        ((comap φ).mapDerivedCategoryFactorsh.inv.app M) ≫
      (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj M) =
    (extendScalars φ).leftDerivedFunctorCounit.app
        (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).counit.app M) := by
  have h₁ := (extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)
    |>.derivedε_fac_app
    (HomotopyCategory.quasiIso (Mod C S) (ComplexShape.up ℤ))
    (extendScalars φ).leftDerivedFunctorCounit (comap φ).rightDerivedFunctorUnit M
  have h₃ := NatTrans.congr_app (comap φ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  simp only [derivedExtendMapDerivedCategoryAdjunction, derivedExtendRestrictAdjunction,
    rightDerivedComapIsoMapDerivedCategory, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app]
  rw [← h₃]
  rw [Functor.whiskerRight_app, Adjunction.derived_counit, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc (extendScalars φ).leftDerivedFunctor
      ((comap φ).rightDerivedFunctorIsoMapDerivedCategory.hom.app _), Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp]
  exact h₁

/-- The unit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `M`,
followed by the counit of the derived extension of scalars, is the levelwise unit. -/
@[reassoc]
lemma derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh
    (M : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Qh.obj M) ≫
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctorCounit.app M) =
    DerivedCategory.Qh.map
        (((extendRestrictAdjunction φ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app M) ≫
      (comap φ).mapDerivedCategoryFactorsh.inv.app
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  apply ((derivedExtendMapDerivedCategoryAdjunction φ).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h := derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh φ
    (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)
  dsimp only [Functor.comp_obj] at h ⊢
  rw [h]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  erw [← Functor.comp_map DerivedCategory.Qh (extendScalars φ).leftDerivedFunctor,
    (extendScalars φ).leftDerivedFunctorCounit.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp]
  erw [Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The counit of the derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` on the image of a complex `M`,
in the form used by `CategoryTheory.Adjunction.mateEquiv_leftDerived_inv_eq`. -/
lemma derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq
    (M : HomotopyCategory (Mod C S) (ComplexShape.up ℤ)) :
    (derivedExtendMapDerivedCategoryAdjunction φ).counit.app (DerivedCategory.Qh.obj M) =
      (extendScalars φ).leftDerivedFunctor.map
          ((comap φ).mapDerivedCategoryFactorsh.hom.app M) ≫
        (extendScalars φ).leftDerivedFunctorCounit.app
          (((comap φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          (((extendRestrictAdjunction φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).counit.app M) := by
  rw [← derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.Mod
