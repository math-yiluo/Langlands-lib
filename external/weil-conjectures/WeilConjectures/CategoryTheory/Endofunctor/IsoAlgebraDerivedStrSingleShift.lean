/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointLift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# The derived structure isomorphism on single complexes and shifts

The derived structure isomorphism `CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso` of
Weil objects (`F (U A) ≅ U A` on the derived category of algebras) is
- on an object `K` placed in degree `0`, the structure isomorphism of `K` placed in degree `0`
  (`derivedStrIso_hom_app_singleFunctor_obj`), through the identifications of the derived
  functors on objects placed in degree zero;
- compatible with the shifts (`NatTrans.CommShift (derivedStrIso F).hom ℤ`), so that on `A⟦n⟧` it
  is the shift of the structure isomorphism of `A` (`derivedStrIso_hom_app_shift`).
These are the formal inputs for reading the Frobenius structure of a shifted Tate twist
`ℚ̄_ℓ(d)[2d]` of a Weil sheaf.
-/

@[expose] public noncomputable section

universe v w

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type*} [Category.{v} C] [Abelian C] (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- The derived structure isomorphism commutes with the shifts. -/
instance commShift_derivedStrIso_hom : NatTrans.CommShift (derivedStrIso F).hom ℤ := by
  rw [show (derivedStrIso F).hom = (Functor.mapDerivedCategoryCompIso (forget F) F).hom ≫
    (Functor.mapDerivedCategoryNatIso (strNatIso F)).hom from rfl]
  infer_instance

/-- The derived structure isomorphism on a shift `A⟦n⟧` is the shift of the derived structure
isomorphism of `A`, through the shift isomorphisms of `D(U)` and `D(F)`. -/
lemma derivedStrIso_hom_app_shift (A : DerivedCategory (IsoAlgebra F)) (n : ℤ) :
    (derivedStrIso F).hom.app (A⟦n⟧) =
      (((forget F).mapDerivedCategory ⋙ F.mapDerivedCategory).commShiftIso n).hom.app A ≫
        ((derivedStrIso F).hom.app A)⟦n⟧' ≫
        ((forget F).mapDerivedCategory.commShiftIso n).inv.app A :=
  NatTrans.app_shift (derivedStrIso F).hom n A

/-- The derived structure isomorphism of an object `K` placed in degree `0` is the structure
isomorphism of `K` placed in degree `0`, through the identifications of `D(U)` and `D(F)` on
objects placed in degree `0`. -/
lemma derivedStrIso_hom_app_singleFunctor_obj (K : IsoAlgebra F) :
    (derivedStrIso F).hom.app ((DerivedCategory.singleFunctor (IsoAlgebra F) 0).obj K) ≫
        ((forget F).mapDerivedCategorySingleFunctor 0).hom.app K =
      F.mapDerivedCategory.map (((forget F).mapDerivedCategorySingleFunctor 0).hom.app K) ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app K.carrier ≫
        (DerivedCategory.singleFunctor C 0).map K.str.hom := by
  have h1 := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor (strNatIso F) K
  have h2 := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor (forget F) F K
  simp only [strNatIso_hom_app] at h1
  simp only [derivedStrIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [h1, ← h2]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra
