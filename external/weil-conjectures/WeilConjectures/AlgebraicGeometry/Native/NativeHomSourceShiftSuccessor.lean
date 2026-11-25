/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # The degree-one recurrence for the raw source-Hom mates

## References

* Stacks Project, Tags 08J9 and 08JC, tensor-Hom adjunction and total-tensor signs
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe v d
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

open CategoryTheory.MonoidalClosed CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {D : Type d} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

private def tensorMate (K : D) (r : ℤ) :
    shiftFunctor D r ⋙ tensorLeft K ≅ tensorLeft (K⟦r⟧) :=
  (tensorLeft K).commShiftIso r ≪≫ (siteHomTensorParameterShift K r).symm

omit [MonoidalClosed D] [MonoidalPreadditive D] in
private theorem tensorMate_add (K Y : D) (r s t : ℤ) (h : r + s = t) :
    (tensorLeft K).map ((shiftFunctorAdd' D s r t ((add_comm s r).trans h)).hom.app Y) ≫
        (tensorMate K r).hom.app (Y⟦s⟧) ≫
        (tensorMate (K⟦r⟧) s).hom.app Y ≫
        ((shiftFunctorAdd' D r s t h).inv.app K ▷ Y) =
      (r * s).negOnePow • (tensorMate K t).hom.app Y := by
  apply (cancel_mono ((siteHomTensorParameterShift K t).hom.app Y)).mp
  have ht := congr_app (congrArg Iso.hom
    (((curriedTensor D).flip.obj Y).commShiftIso_add' h)) K
  simp only [CommShift.isoAdd'_hom_app] at ht
  have hc := congr_app (congrArg Iso.hom
    ((tensorLeft K).commShiftIso_add' ((add_comm s r).trans h))) Y
  simp only [CommShift.isoAdd'_hom_app] at hc
  have hi := (curriedTensor D).commShift₂_comm CommShift₂Setup.int K Y r s
  simp only [CommShift₂Setup.int_ε, CatCenter.app_neg_one_zpow,
    Linear.comp_units_smul, Category.comp_id] at hi
  dsimp only [tensorMate, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Linear.units_smul_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  have ht' : ((shiftFunctorAdd' D r s t h).inv.app K ▷ Y) ≫
      (siteHomTensorParameterShift K t).hom.app Y =
        (siteHomTensorParameterShift (K⟦r⟧) s).hom.app Y ≫
        ((siteHomTensorParameterShift K r).hom.app Y)⟦s⟧' ≫
        (shiftFunctorAdd' D r s t h).inv.app (K ⊗ Y) := by
    simp only [siteHomTensorParameterShift, NatIso.ofComponents_hom_app,
      Iso.app_hom] at *
    rw [ht]
    change (((curriedTensor D).flip.obj Y).map _ ≫ _) = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [ht', Iso.inv_hom_id_app_assoc]
  simp only [siteHomTensorParameterShift, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% hi]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [curriedTensor_obj_obj] at hi hc ⊢
  simp only [shiftComm, shiftFunctorComm_eq D r s t h, Iso.app_inv,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]
  rw [← hc]

private def shiftAdj (r a : ℤ) (h : r + a = 0) :
    shiftFunctor D r ⊣ shiftFunctor D a :=
  (shiftEquiv' D r a h).toAdjunction

omit [Preadditive D] [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int] in
private theorem shift_add_mate (r s t a b c : ℤ)
    (hr : r + a = 0) (hs : s + b = 0) (ht : t + c = 0) (h : r + s = t) :
    conjugateEquiv
      ((shiftAdj (D := D) s b hs).comp (shiftAdj r a hr))
      (shiftAdj t c ht)
      (shiftFunctorAdd' D s r t ((add_comm s r).trans h)).hom =
        (shiftFunctorAdd' D a b c (by omega)).inv := by
  ext Y
  apply ((shiftAdj (D := D) t c ht).homEquiv _ Y).symm.injective
  rw [Adjunction.homEquiv_counit, conjugateEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Adjunction.comp_counit_app]
  change (shiftFunctorAdd' D s r t ((add_comm s r).trans h)).hom.app (Y⟦a⟧⟦b⟧) ≫
      ((shiftFunctorCompIsoId D b s (by omega)).hom.app (Y⟦a⟧))⟦r⟧' ≫
        (shiftFunctorCompIsoId D a r (by omega)).hom.app Y =
    ((shiftFunctorAdd' D a b c (by omega)).inv.app Y)⟦t⟧' ≫
      (shiftFunctorCompIsoId D c t (by omega)).hom.app Y
  rw [shiftFunctorCompIsoId_add'_hom_app s r t b a c
    (by omega) (by omega) (by omega) ((add_comm s r).trans h)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

omit [MonoidalPreadditive D] in
private theorem sourceShift_conjugate (K : D) (n : ℤ) :
    (siteHomSourceShift K n).hom =
      conjugateEquiv (ihom.adjunction (K⟦n⟧))
        ((shiftAdj n (-n) (add_neg_cancel n)).comp (ihom.adjunction K))
        (tensorMate K n).hom := by
  unfold siteHomSourceShift Adjunction.rightAdjointUniq
  ext M
  simp [shiftAdj, tensorMate, conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit]

private def sourceMate (K : D) (r a : ℤ) (h : r + a = 0) :
    ihom (K⟦r⟧) ⟶ ihom K ⋙ shiftFunctor D a :=
  conjugateEquiv (ihom.adjunction (K⟦r⟧))
    ((shiftAdj r a h).comp (ihom.adjunction K))
    (tensorMate K r).hom

omit [MonoidalPreadditive D] in
private theorem sourceMate_transport (K : D) (r a : ℤ) (h : r + a = 0) (ha : -r = a) :
    sourceMate K r a h = (siteHomSourceShift K r).hom ≫
      whiskerLeft (ihom K) (eqToIso (congrArg (shiftFunctor D) ha)).hom := by
  subst a
  rw [sourceShift_conjugate]
  ext Y
  simp only [sourceMate, eqToIso_refl, Iso.refl_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app]
  erw [Category.comp_id]

omit [MonoidalPreadditive D] in
private theorem oppositeSource_eq (K : D) (n : ℤ) :
    (siteHomOppositeSourceShift K n).hom = sourceMate K (-n) n (neg_add_cancel n) := by
  rw [sourceMate_transport K (-n) n (neg_add_cancel n) (neg_neg n)]
  simp only [siteHomOppositeSourceShift, Iso.trans_hom, Functor.isoWhiskerLeft_hom]

private theorem sourceMate_add (K : D) (r s t a b c : ℤ)
    (hr : r + a = 0) (hs : s + b = 0) (ht : t + c = 0) (h : r + s = t) :
    pre ((shiftFunctorAdd' D r s t h).inv.app K) ≫
        sourceMate (K⟦r⟧) s b hs ≫
        whiskerRight (sourceMate K r a hr) (shiftFunctor D b) ≫
        (Functor.associator (ihom K) (shiftFunctor D a) (shiftFunctor D b)).hom ≫
        whiskerLeft (ihom K) (shiftFunctorAdd' D a b c (by omega)).inv =
      (r * s).negOnePow • sourceMate K t c ht := by
  let ar := shiftAdj (D := D) r a hr
  let as' := shiftAdj (D := D) s b hs
  let adjT := shiftAdj (D := D) t c ht
  let α : shiftFunctor D t ⋙ tensorLeft K ⟶ tensorLeft (K⟦t⟧) :=
    whiskerRight (shiftFunctorAdd' D s r t ((add_comm s r).trans h)).hom (tensorLeft K) ≫
      (Functor.associator (shiftFunctor D s) (shiftFunctor D r) (tensorLeft K)).hom ≫
      whiskerLeft (shiftFunctor D s) (tensorMate K r).hom ≫
      (tensorMate (K⟦r⟧) s).hom ≫
      (tensoringLeft D).map ((shiftFunctorAdd' D r s t h).inv.app K)
  have hα : α = (r * s).negOnePow • (tensorMate K t).hom := by
    ext Y
    simpa [α] using tensorMate_add K Y r s t h
  have hm :
      pre ((shiftFunctorAdd' D r s t h).inv.app K) ≫
          sourceMate (K⟦r⟧) s b hs ≫
          whiskerRight (sourceMate K r a hr) (shiftFunctor D b) ≫
          (Functor.associator (ihom K) (shiftFunctor D a) (shiftFunctor D b)).hom ≫
          whiskerLeft (ihom K) (shiftFunctorAdd' D a b c (by omega)).inv =
        conjugateEquiv (ihom.adjunction (K⟦t⟧)) (adjT.comp (ihom.adjunction K)) α := by
    rw [show (shiftFunctorAdd' D a b c (by omega)).inv =
      conjugateEquiv (as'.comp ar) adjT
        (shiftFunctorAdd' D s r t ((add_comm s r).trans h)).hom from
          (shift_add_mate r s t a b c hr hs ht h).symm]
    rw [← conjugateEquiv_whiskerRight (as'.comp ar) adjT (ihom.adjunction K)]
    rw [show (Functor.associator (ihom K) (shiftFunctor D a)
      (shiftFunctor D b)).hom = conjugateEquiv
        (as'.comp (ar.comp (ihom.adjunction K)))
        ((as'.comp ar).comp (ihom.adjunction K))
        (Functor.associator (shiftFunctor D s) (shiftFunctor D r) (tensorLeft K)).hom from
          (conjugateEquiv_associator_hom as' ar (ihom.adjunction K)).symm]
    unfold sourceMate pre
    rw [← conjugateEquiv_whiskerLeft (ihom.adjunction (K⟦r⟧))
      (ar.comp (ihom.adjunction K)) as']
    dsimp only [ar, as', adjT, Functor.comp_obj]
    simp only [conjugateEquiv_comp, Category.assoc]
    rfl
  rw [hm, hα]
  have := (ihom.adjunction K).right_adjoint_additive
  ext Y
  simp [sourceMate, adjT, conjugateEquiv_apply_app, Linear.comp_units_smul,
    Linear.units_smul_comp]

omit [Preadditive D] [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int] in
private theorem opposite_add_unop (X : Dᵒᵖ) (m n : ℤ) :
    ((shiftFunctorAdd Dᵒᵖ m n).hom.app X).unop =
      (shiftFunctorAdd' D (-m) (-n) (-(m + n)) (by omega)).inv.app X.unop := by
  rw [← shiftFunctorAdd'_eq_shiftFunctorAdd,
    shiftFunctorAdd'_op_hom_app X m n (m + n) rfl (-m) (-n) (-(m + n))
      (add_neg_cancel m) (add_neg_cancel n) (add_neg_cancel (m + n))]
  simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.comp_obj, Functor.op_obj, unop_comp, Quiver.Hom.unop_op,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id]
  change 𝟙 (X.unop⟦-m⟧⟦-n⟧) ≫ 𝟙 (X.unop⟦-m⟧⟦-n⟧) ≫
      (shiftFunctorAdd' D (-m) (-n) (-(m + n)) (by omega)).inv.app X.unop ≫
        𝟙 (X.unop⟦-(m + n)⟧) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Increasing the opposite source shift by one introduces the sign `(-1)^m`. -/
theorem siteHom_opposite_source_shift_successor (M : D) (m : ℤ) (X : Dᵒᵖ) :
    (siteHomOppositeSourceShift X.unop (m + 1)).hom.app M =
      m.negOnePow •
        ((MonoidalClosed.internalHom.flip.obj M).map
            ((shiftFunctorAdd Dᵒᵖ m 1).hom.app X) ≫
          (siteHomOppositeSourceShift (X⟦m⟧).unop 1).hom.app M ≫
          ((siteHomOppositeSourceShift X.unop m).hom.app M)⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd D m 1).inv.app ((ihom X.unop).obj M)) := by
  change (siteHomOppositeSourceShift X.unop (m + 1)).hom.app M =
    m.negOnePow •
      ((pre (((shiftFunctorAdd Dᵒᵖ m 1).hom.app X).unop)).app M ≫
        (siteHomOppositeSourceShift (X.unop⟦-m⟧) 1).hom.app M ≫
        ((siteHomOppositeSourceShift X.unop m).hom.app M)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd D m 1).inv.app ((ihom X.unop).obj M))
  have hh := congr_app (sourceMate_add X.unop (-m) (-1) (-(m + 1)) m 1 (m + 1)
    (neg_add_cancel m) (neg_add_cancel 1) (neg_add_cancel (m + 1)) (by omega)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, neg_mul_neg, mul_one,
    NatTrans.app_units_zsmul] at hh
  have hh' := congrArg (fun z ↦ m.negOnePow • z) hh
  simp only [smul_smul, Int.units_mul_self, one_smul] at hh'
  rw [opposite_add_unop]
  simp only [oppositeSource_eq, shiftFunctorAdd'_eq_shiftFunctorAdd] at hh' ⊢
  exact hh'.symm

end AlgebraicGeometry.ProEtale
