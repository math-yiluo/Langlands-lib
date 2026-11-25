/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit

/-!
# The transitivity of the derived extension of scalars along flat morphisms

Let `φ : R ⟶ S`, `ψ : S ⟶ T` and `χ : R ⟶ T` be morphisms of commutative algebra objects with
`φ ≫ ψ = χ`, along which extension of scalars is exact. The transitivity isomorphism
`Mod.derivedExtendScalarsCompIso` of the derived extensions of scalars, defined as the conjugate
of the composition isomorphism of the restrictions of scalars, is also the one obtained from the
underived transitivity isomorphism `Mod.extendScalarsComp` by applying the left derived functors
of the exact functors levelwise (`Functor.leftDerivedFunctorCompIso`,
`Functor.leftDerivedFunctorNatIso`): this is
`Mod.leftDerivedFunctorCompIso_symm_trans_leftDerivedFunctorNatIso_eq`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]
  [PreservesFiniteLimits (extendScalars φ)] [PreservesFiniteLimits (extendScalars ψ)]
  [PreservesFiniteLimits (extendScalars χ)]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T]
  [PreservesFiniteLimits (extendScalars φ)] [PreservesFiniteLimits (extendScalars ψ)]
  [PreservesFiniteLimits (extendScalars χ)] in
/-- The unit of extension of scalars along `χ = φ ≫ ψ`, followed by the transitivity
isomorphism `Mod.extendScalarsComp`, is the composite of the units along `φ` and `ψ`, followed by
the composition isomorphism of the restrictions of scalars. -/
lemma extendRestrictAdjunction_unit_app_comp_map_extendScalarsComp (h : φ ≫ ψ = χ)
    (M : Mod C R) :
    (extendRestrictAdjunction χ).unit.app M ≫ (comap χ).map
        (((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).inv.app M) =
      (extendRestrictAdjunction φ).unit.app M ≫
        (comap φ).map ((extendRestrictAdjunction ψ).unit.app ((extendScalars φ).obj M)) ≫
        ((comapComp φ ψ).symm ≪≫ comapCongr h).hom.app _ := by
  have h₁ := congrArg Mod.Hom.hom (Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (φ ≫ ψ)) (((extendRestrictAdjunction φ).comp
      (extendRestrictAdjunction ψ)).ofNatIsoRight (comapComp φ ψ).symm) M)
  have h₂ := congrArg Mod.Hom.hom (Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (φ ≫ ψ))
    ((extendRestrictAdjunction χ).ofNatIsoRight (comapCongr h).symm) M)
  have h₃ : ((extendScalarsIsoOfEq h).hom.app M).hom ≫ ((extendScalarsIsoOfEq h).inv.app M).hom =
      𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id_app]
    rfl
  apply Mod.hom_ext
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app, Mod.comp_hom',
    Mod.comap_map_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Mod.comapComp_inv_app_hom,
    Mod.comapCongr_hom_app_hom, Mod.comapCongr_inv_app_hom,
    Category.assoc] at h₁ h₂ ⊢
  erw [Category.comp_id] at h₁ h₂
  erw [Category.comp_id, Category.comp_id]
  have h₄ : ((extendRestrictAdjunction χ).unit.app M).hom ≫
      ((extendScalarsIsoOfEq h).inv.app M).hom =
      ((extendRestrictAdjunction (φ ≫ ψ)).unit.app M).hom := by
    erw [← h₂, Category.assoc, h₃, Category.comp_id]
  erw [reassoc_of% h₄]
  exact h₁

/-- On the image of a homotopy class `X`, the levelwise transitivity isomorphism of the derived
extensions of scalars is computed, modulo the counits of the left derived functors, by the
levelwise image of the transitivity isomorphism `Mod.extendScalarsComp`. -/
@[reassoc]
lemma leftDerivedFunctorNatIso_inv_app_Qh_obj_comp_counit (h : φ ≫ ψ = χ)
    (X : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    ((Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h)).inv.app
          (DerivedCategory.Qh.obj X) ≫
      (extendScalars ψ).leftDerivedFunctor.map
        ((extendScalars φ).leftDerivedFunctorCounit.app X) ≫
      (extendScalars ψ).leftDerivedFunctorCounit.app
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) =
    (extendScalars χ).leftDerivedFunctorCounit.app X ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).inv
          (ComplexShape.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ extendScalars ψ))
        (ComplexShape.up ℤ)).inv.app X) := by
  simp only [Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso, Iso.trans_inv,
    Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hψ := NatTrans.congr_app
    (extendScalars ψ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
  have hφ := NatTrans.congr_app
    (extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hψ hφ
  erw [← (extendScalars ψ).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  rw [← hψ]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← hφ, Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp]
  rw [← cancel_mono (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl (extendScalars φ ⋙ extendScalars ψ)) (ComplexShape.up ℤ)).hom.app X))]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  have hχ := NatTrans.congr_app
    (extendScalars χ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hχ
  rw [Category.comp_id, Functor.mapDerivedCategoryCompIso_fach,
    ← Functor.mapDerivedCategoryNatIso_symm, ← hχ, Category.assoc]
  congr 1
  exact Functor.mapDerivedCategoryNatIso_fach
    ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).symm X

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj R]
  [IsCommMonObj S] [IsCommMonObj T] [PreservesFiniteLimits (extendScalars φ)]
  [PreservesFiniteLimits (extendScalars ψ)] [PreservesFiniteLimits (extendScalars χ)] in
/-- On the image of a homotopy class `Y`, the composition isomorphism
`Mod.mapDerivedCategoryComapCompIso` of the restrictions of scalars is computed by the levelwise
composition isomorphism. -/
@[reassoc]
lemma mapDerivedCategoryComapCompIso_hom_app_Qh_obj_comp_factorsh (h : φ ≫ ψ = χ)
    (Y : HomotopyCategory (Mod C T) (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComapCompIso φ ψ χ h).hom.app (DerivedCategory.Qh.obj Y) ≫
        (comap χ).mapDerivedCategoryFactorsh.hom.app Y =
      (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.hom.app Y) ≫
        (comap φ).mapDerivedCategoryFactorsh.hom.app
          (((comap ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (comap ψ ⋙ comap φ)) (ComplexShape.up ℤ)).hom.app Y ≫
          (NatTrans.mapHomotopyCategory ((comapComp φ ψ).symm ≪≫ comapCongr h).hom
            (ComplexShape.up ℤ)).app Y) := by
  rw [mapDerivedCategoryComapCompIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Functor.mapDerivedCategoryNatIso_fach,
    ← cancel_epi (((comap ψ).mapDerivedCategoryCompIso (comap φ)).inv.app _),
    Iso.inv_hom_id_app_assoc,
    ← Functor.mapDerivedCategoryCompIso_fach_assoc, Functor.map_comp]

/-- The form of `Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_comp_map_inv_app` on the
image of a homotopy class. -/
lemma derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh_obj_comp_map_inv_app
    (h : φ ≫ ψ = χ) (X : HomotopyCategory (Mod C R) (ComplexShape.up ℤ)) :
    (derivedExtendMapDerivedCategoryAdjunction χ).unit.app (DerivedCategory.Qh.obj X) ≫
        (comap χ).mapDerivedCategory.map
          (((Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
            Functor.leftDerivedFunctorNatIso _
              ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h)).inv.app
                (DerivedCategory.Qh.obj X)) =
      ((derivedExtendMapDerivedCategoryAdjunction φ).comp
          (derivedExtendMapDerivedCategoryAdjunction ψ)).unit.app (DerivedCategory.Qh.obj X) ≫
        (mapDerivedCategoryComapCompIso φ ψ χ h).hom.app _ := by
  rw [← cancel_mono ((comap χ).mapDerivedCategory.map
      ((extendScalars ψ).leftDerivedFunctor.map
        ((extendScalars φ).leftDerivedFunctorCounit.app X) ≫
      (extendScalars ψ).leftDerivedFunctorCounit.app
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
      (comap χ).mapDerivedCategoryFactorsh.hom.app
        (((extendScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)))]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, leftDerivedFunctorNatIso_inv_app_Qh_obj_comp_counit,
    Functor.map_comp, Category.assoc]
  have hn := (comap χ).mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h).inv
      (ComplexShape.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ extendScalars ψ))
        (ComplexShape.up ℤ)).inv.app X)
  erw [hn, reassoc_of% (derivedExtendMapDerivedCategoryAdjunction_unit_app_fac χ X)]
  rw [Functor.comp_map, ← Functor.map_comp, Adjunction.comp_unit_app]
  have hk := (mapDerivedCategoryComapCompIso φ ψ χ h).hom.naturality
    ((extendScalars ψ).leftDerivedFunctor.map ((extendScalars φ).leftDerivedFunctorCounit.app X) ≫
      (extendScalars ψ).leftDerivedFunctorCounit.app
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
  have hin : (derivedExtendMapDerivedCategoryAdjunction ψ).unit.app
        ((extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Qh.obj X)) ≫
      (comap ψ).mapDerivedCategory.map
        ((extendScalars ψ).leftDerivedFunctor.map
          ((extendScalars φ).leftDerivedFunctorCounit.app X) ≫
        (extendScalars ψ).leftDerivedFunctorCounit.app
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
      (comap ψ).mapDerivedCategoryFactorsh.hom.app
        (((extendScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
      (extendScalars φ).leftDerivedFunctorCounit.app X ≫
        DerivedCategory.Qh.map (((extendRestrictAdjunction ψ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app
            (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
    rw [Functor.map_comp, Category.assoc]
    erw [Adjunction.unit_naturality_assoc]
    erw [derivedExtendMapDerivedCategoryAdjunction_unit_app_fac]
  erw [← reassoc_of% hk, mapDerivedCategoryComapCompIso_hom_app_Qh_obj_comp_factorsh]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hin,
    Functor.map_comp (comap φ).mapDerivedCategory, Category.assoc]
  have hn' := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
    (((extendRestrictAdjunction ψ).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
      (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
  erw [reassoc_of% hn', reassoc_of% (derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ X)]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have c₁ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ extendScalars ψ))
      (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj K) =
      𝟙 _ := rfl
  have c₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (comap ψ ⋙ comap φ))
      (ComplexShape.up ℤ)).hom.app (((extendScalars ψ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)).obj K))) = 𝟙 _ := rfl
  erw [c₁, c₂, Category.comp_id, Category.id_comp, NatTrans.mapHomotopyCategory_app,
    NatTrans.mapHomotopyCategory_app, Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f]
  exact extendRestrictAdjunction_unit_app_comp_map_extendScalarsComp φ ψ χ h (K.X n)

/-- The unit of the derived adjunction along `χ`, followed by the levelwise transitivity
isomorphism, is the unit of the composite derived adjunction followed by the composition
isomorphism `Mod.mapDerivedCategoryComapCompIso` of the restrictions of scalars. -/
lemma derivedExtendMapDerivedCategoryAdjunction_unit_app_comp_map_inv_app (h : φ ≫ ψ = χ)
    (K : DerivedCategory (Mod C R)) :
    (derivedExtendMapDerivedCategoryAdjunction χ).unit.app K ≫
        (comap χ).mapDerivedCategory.map
          (((Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
            Functor.leftDerivedFunctorNatIso _
              ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h)).inv.app K) =
      ((derivedExtendMapDerivedCategoryAdjunction φ).comp
          (derivedExtendMapDerivedCategoryAdjunction ψ)).unit.app K ≫
        (mapDerivedCategoryComapCompIso φ ψ χ h).hom.app _ := by
  have H := Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ))
    (τ := (derivedExtendMapDerivedCategoryAdjunction χ).unit ≫ Functor.whiskerRight
      ((Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h)).inv
      (comap χ).mapDerivedCategory)
    (τ' := ((derivedExtendMapDerivedCategoryAdjunction φ).comp
        (derivedExtendMapDerivedCategoryAdjunction ψ)).unit ≫
      Functor.whiskerLeft _ (mapDerivedCategoryComapCompIso φ ψ χ h).hom)
    (derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh_obj_comp_map_inv_app φ ψ χ h)
  exact NatTrans.congr_app H K

/-- For flat `φ`, `ψ` and `χ = φ ≫ ψ`, the transitivity isomorphism of the derived extensions of
scalars obtained levelwise from `Mod.extendScalarsComp` is the inverse of the conjugate
`Mod.derivedExtendScalarsCompIso` of the composition isomorphism of the restrictions of
scalars. -/
theorem leftDerivedFunctorCompIso_symm_trans_leftDerivedFunctorNatIso_eq (h : φ ≫ ψ = χ) :
    (Functor.leftDerivedFunctorCompIso (extendScalars φ) (extendScalars ψ)).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          ((extendScalarsComp φ ψ).symm ≪≫ extendScalarsIsoOfEq h) =
      (derivedExtendScalarsCompIso φ ψ χ h).symm := by
  rw [← Iso.symm_symm_eq (_ ≪≫ _), Iso.symm_eq_iff]
  refine Iso.ext (NatTrans.ext (funext fun K ↦ ?_))
  apply ((derivedExtendMapDerivedCategoryAdjunction χ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Iso.symm_hom,
    derivedExtendMapDerivedCategoryAdjunction_unit_app_comp_map_inv_app φ ψ χ h]
  exact unit_conjugateEquiv_symm _ _ _ K

end CategoryTheory.Mod
