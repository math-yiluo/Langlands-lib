/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.BoundedKunnethSpectralSequence
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Compatibility of coefficient actions with localization
Source: Stacks Project, Tag 0H7Z, simple-tor-product.
(blueprint: lem-pur-kunneth-derived-coefficient-action)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory
variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The single-object unit identification agrees with the lax unit of localization.
Source: Stacks Project, Tags 064L and 06Y0.
(blueprint: lem-pur-kunneth-derived-coefficient-action)
Proof: expand the unit identification. The inverse consists of the unit of Qh, its image
of the quotient unit, and the quotient comparison, which is precisely the unit of Q. -/
theorem singleFunctorObjUnitIso_inv_comp :
    (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} R)).inv ≫
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.app
        (ModuleCat.of R R) =
      Functor.LaxMonoidal.ε (DerivedCategory.Q (C := ModuleCat.{u} R)) := by
  unfold DerivedCategory.singleFunctorObjUnitIso
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Category.assoc,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Functor.mapIso_inv, Iso.symm_inv, Functor.Monoidal.εIso_hom, asIso_hom]
  simp only [← Category.assoc]
  erw [Category.comp_id, Category.comp_id]
  rfl

/-- Localization sends the ordinary coefficient cochain map to the derived coefficient
map followed by its tensor-model comparison.
Source: Stacks Project, Tag 0H7Z, simple-tor-product.
(blueprint: lem-pur-kunneth-derived-coefficient-action)
Proof: naturality of the single-to-localization comparison reduces the coefficient map
to Q of the single coefficient map. The unit comparison is the lax unit. Lax tensorator
naturality and its right unit axiom then give Q of the ordinary right-unitor formula. -/
theorem derived_model_coefficient_action
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) (a : M) :
    ((ρ_ (DerivedCategory.Q.obj P)).inv ≫
      DerivedCategory.Q.obj P ◁
        ((DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} R)).inv ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a)))) ≫
      DerivedCategory.Q.obj P ◁
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.app M ≫
      laxDerivedTensorMap R P
        ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M) =
      DerivedCategory.Q.map ((ρ_ P).inv ≫ P ◁
        (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a))) := by
  have hu := singleFunctorObjUnitIso_inv_comp R
  dsimp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app] at hu
  erw [Category.comp_id] at hu
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    whiskerLeft_id, Category.id_comp]
  rw [hu, Category.assoc]
  change (ρ_ (DerivedCategory.Q.obj P)).inv ≫
      DerivedCategory.Q.obj P ◁ (Functor.LaxMonoidal.ε DerivedCategory.Q ≫
        DerivedCategory.Q.map ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R M a)))) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P _ = _
  rw [whiskerLeft_comp_assoc, Functor.LaxMonoidal.μ_natural_right,
    Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← Functor.map_comp]

end CategoryTheory
