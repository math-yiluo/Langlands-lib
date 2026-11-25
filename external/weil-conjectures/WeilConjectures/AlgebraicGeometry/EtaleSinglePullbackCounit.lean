/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # The canonical single/pullback comparison and the exact derived counit -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

/-- The prescribed derived single/pullback map factors through the derived counit.
Source: Stacks, Cohomology on Sites, Tag 06YY; the exact-functor comparisons
leftDerivedFunctorIsoMapDerivedCategory and mapDerivedCategorySingleFunctor.
(auxiliary; not a blueprint node).
Proof: express the counit using leftDerivedFunctorIsoMapDerivedCategory_hom_fac.
Its naturality moves the single/Qh comparison past the exact-functor comparison.
Expand mapDerivedCategoryFactorsh and mapDerivedCategorySingleFunctor. The mapped
inverse and forward quotient/Qh comparisons cancel. The homotopy functor's quotient
comparison has identity components. Finally, naturality of quotientCompQhIso moves
the termwise single comparison past its inverse component. The remaining composite
is exactly singleFunctorCompLeftDerivedUpperStarIso followed by singleFunctorObjIsoQh. -/
theorem singleFunctorObjIsoQh_pullback_counit
    {X' : AlgebraicGeometry.Scheme.{u}} (v : X' ⟶ X)
    (L : Sheaf X.smallEtaleTopology B) :
    (upperStar B v).leftDerivedFunctor.map (singleFunctorObjIsoQh L).hom ≫
      (upperStar B v).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (upperStar B v)
          (.up ℤ) 0).hom.app L)) =
      (singleFunctorCompLeftDerivedUpperStarIso B v).hom.app L ≫
        (singleFunctorObjIsoQh ((upperStar B v).obj L)).hom := by
  rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_obj, singleFunctorObjIsoQh, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.map_comp, Functor.mapHomotopyCategory_obj,
    Functor.mapDerivedCategoryFactorsh_hom_app, DerivedCategory.Q_obj_single_obj,
    Category.assoc, singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Functor.mapDerivedCategorySingleFunctor,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Iso.inv_hom_id_app_assoc, NatIso.cancel_natIso_hom_left]
  erw [← (upperStar B v).mapDerivedCategory.map_comp_assoc
    ((DerivedCategory.quotientCompQhIso (Sheaf X.smallEtaleTopology B)).inv.app _)
    ((DerivedCategory.quotientCompQhIso (Sheaf X.smallEtaleTopology B)).hom.app _),
    Iso.inv_hom_id_app]
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality]
  erw [Category.id_comp]

end AlgebraicGeometry.Etale
