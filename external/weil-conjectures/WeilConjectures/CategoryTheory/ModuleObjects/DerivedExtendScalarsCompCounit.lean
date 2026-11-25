/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!

# The transitivity of the derived extension of scalars and the counits

For morphisms `φ : R ⟶ S`, `ψ : S ⟶ T` of commutative algebra objects, the transitivity
isomorphism `T ⊗ᴸ_R - ≅ (T ⊗ᴸ_S -) ∘ (S ⊗ᴸ_R -)` (`Mod.derivedExtendScalarsCompIso`), defined as
a conjugate, is compatible with the counits of the left derived functors and the underived
transitivity isomorphism `Mod.extendScalarsComp`
(`Mod.derivedExtendScalarsCompIso_hom_app_comp_counit`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj R] in
/-- The composition isomorphism of the levelwise restrictions of scalars on the image of an
object of the homotopy category. -/
@[reassoc]
lemma mapDerivedCategoryComapCompIso_hom_app_Qh_comp_factorsh
    (Z : HomotopyCategory (Mod C T) (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom.app (DerivedCategory.Qh.obj Z) ≫
        (comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.hom.app Z =
      (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.hom.app Z) ≫
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Z) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (comap ψ ⋙ comap φ)) (ComplexShape.up ℤ)).hom.app Z) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          ((comapComp φ ψ).inv ≫ (comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).hom)
            (ComplexShape.up ℤ)).app Z) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach (comap ψ) (comap φ) Z
  have h₂ := Functor.mapDerivedCategoryNatIso_fach
    ((comapComp φ ψ).symm ≪≫ comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)) Z
  simp only [mapDerivedCategoryComapCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at h₂ ⊢
  rw [h₂, ← reassoc_of% h₁, Iso.hom_inv_id_app_assoc]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
/-- The underived transitivity isomorphism `Mod.extendScalarsComp` is compatible with the units
of the extension-restriction adjunctions. -/
lemma extendRestrictAdjunction_unit_app_comp_extendScalarsComp_inv (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M ≫
        (comap φ).map ((extendRestrictAdjunction ψ).unit.app ((extendScalars φ).obj M)) ≫
        (comap φ).map ((comap ψ).map ((extendScalarsComp φ ψ).inv.app M)) ≫
        (comapComp φ ψ).inv.app _ =
      (extendRestrictAdjunction (φ ≫ ψ)).unit.app M := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (extendRestrictAdjunction (φ ≫ ψ))
    (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm) M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Adjunction.comp_unit_app] at h
  have n := (comapComp φ ψ).inv.naturality ((extendScalarsComp φ ψ).inv.app M)
  simp only [Functor.comp_map] at n
  simp only [Functor.comp_obj] at h n ⊢
  rw [n, ← reassoc_of% h, ← Functor.map_comp]
  erw [Iso.hom_inv_id_app]
  rw [Functor.map_id, Category.comp_id]

/-- **The transitivity of the derived extension of scalars is compatible with the counits**:
on the image of an object `K` of the homotopy category, `Mod.derivedExtendScalarsCompIso`
followed by the counits of `L(Ext_φ)` and `L(Ext_ψ)` is the counit of `L(Ext_{φ ≫ ψ})` followed
by the underived transitivity isomorphism `Mod.extendScalarsComp`. -/
@[reassoc]
lemma derivedExtendScalarsCompIso_hom_app_comp_counit
    (K : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    (derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).hom.app (DerivedCategory.Qh.obj K) ≫
        (extendScalars ψ).leftDerivedFunctor.map
          ((extendScalars φ).leftDerivedFunctorCounit.app K) ≫
        (extendScalars ψ).leftDerivedFunctorCounit.app
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)).hom.app K) =
      (extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit.app K := by
  apply ((derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← cancel_mono ((comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.hom.app _), Category.assoc,
    Category.assoc, derivedExtendMapDerivedCategoryAdjunction_unit_app_fac]
  have hc := unit_conjugateEquiv_symm ((derivedExtendMapDerivedCategoryAdjunction φ).comp
    (derivedExtendMapDerivedCategoryAdjunction ψ))
    (derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ))
    (mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom (DerivedCategory.Qh.obj K)
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  erw [← hc]
  simp only [Category.assoc]
  rw [← (mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom.naturality_assoc,
    mapDerivedCategoryComapCompIso_hom_app_Qh_comp_factorsh, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Category.assoc]
  have hin : (derivedExtendMapDerivedCategoryAdjunction ψ).unit.app
        ((extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫
      (comap ψ).mapDerivedCategory.map
        ((extendScalars ψ).leftDerivedFunctor.map
            ((extendScalars φ).leftDerivedFunctorCounit.app K) ≫
          (extendScalars ψ).leftDerivedFunctorCounit.app
            (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)).hom.app K)) ≫
      (comap ψ).mapDerivedCategoryFactorsh.hom.app
        (((extendScalars (φ ≫ ψ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (extendScalars φ).leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map (((extendRestrictAdjunction ψ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app (((extendScalars φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso
            (extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)).hom.app K)) := by
    have n1 := (comap ψ).mapDerivedCategoryFactorsh.hom.naturality
      ((Functor.mapHomotopyCategoryCompIso (extendScalarsComp φ ψ).symm
        (ComplexShape.up ℤ)).hom.app K)
    have n2 := (derivedExtendMapDerivedCategoryAdjunction ψ).unit.naturality
      ((extendScalars φ).leftDerivedFunctorCounit.app K)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n1 n2
    have n3 := derivedExtendMapDerivedCategoryAdjunction_unit_app_fac ψ
      (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
    simp only [Functor.map_comp, Category.assoc]
    rw [n1, ← reassoc_of% n2, reassoc_of% n3]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hin]
  have n4 := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
    ((((extendRestrictAdjunction ψ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
      (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
      ((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (extendScalarsComp φ ψ).symm
          (ComplexShape.up ℤ)).hom.app K))
  have n5 := derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ K
  simp only [Functor.comp_obj, Functor.comp_map] at n4
  rw [← DerivedCategory.Qh.map_comp, Functor.map_comp, Category.assoc, reassoc_of% n4,
    reassoc_of% n5, ← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp,
    ← DerivedCategory.Qh.map_comp]
  congr 1
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  have hcI : (Functor.mapHomotopyCategoryCompIso (extendScalarsComp φ ψ).symm
      (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj P) =
      (HomotopyCategory.quotient (Mod C T) (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (extendScalarsComp φ ψ).symm
          (ComplexShape.up ℤ)).hom.app P) := rfl
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  erw [Category.id_comp, hcI,
    NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
    ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
    NatTrans.comp_app, comp_hom']
  rw [← extendRestrictAdjunction_unit_app_comp_extendScalarsComp_inv φ ψ (P.X n)]
  simp only [comp_hom', comap_map_hom, Category.assoc, comapCongr_hom_app_hom]
  erw [Category.comp_id]
  rfl


/-- `Mod.derivedExtendScalarsCompIso_hom_app_comp_counit`, for the inverse. -/
@[reassoc]
lemma derivedExtendScalarsCompIso_inv_app_comp_counit
    (K : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    (derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).inv.app (DerivedCategory.Qh.obj K) ≫
        (extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit.app K =
      (extendScalars ψ).leftDerivedFunctor.map
          ((extendScalars φ).leftDerivedFunctorCounit.app K) ≫
        (extendScalars ψ).leftDerivedFunctorCounit.app
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (extendScalarsComp φ ψ).symm (ComplexShape.up ℤ)).hom.app K) := by
  rw [← derivedExtendScalarsCompIso_hom_app_comp_counit, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Mod
