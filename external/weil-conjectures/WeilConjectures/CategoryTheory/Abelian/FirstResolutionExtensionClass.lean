/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# The first extension class of an injective resolution

Source: Stacks Project, Tags 06XR and 06XV, resolution computation and extension classes.
(blueprint: lem-amb-first-resolution-extension-class).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {G : C} (R : InjectiveResolution G)
  (w₀ : R.ι.f 0 ≫ R.cocomplex.toCycles 0 1 = 0)
  (hS : (ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) w₀).ShortExact)

omit [HasExt C] in
set_option backward.defeqAttrib.useBackward true in
private lemma firstBoundary_homotopy :
    let S := ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) w₀
    let S' := S.map (CochainComplex.singleFunctor C 0)
    let z := Cocycle.fromSingleMk
      (R.cocomplex.iCycles 1 ≫ (R.cochainComplexXIso 1 1 rfl).inv)
      (zero_add (1 : ℤ)) 2 rfl (by
        simp [R.cochainComplex_d 1 2 1 2 rfl rfl, Category.assoc])
    Nonempty (Homotopy
      (CochainComplex.mappingCone.descShortComplex S' ≫ Cocycle.equivHomShift.symm z)
      (-((CochainComplex.mappingCone.triangle S'.f).mor₃ ≫ R.ι'⟦(1 : ℤ)⟧'))) := by
  dsimp only
  let S := ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) w₀
  let γ : Cochain ((CochainComplex.singleFunctor C 0).obj (R.cocomplex.X 0))
      (R.cochainComplex⟦(1 : ℤ)⟧) (-1) :=
    Cochain.fromSingleMk
      (-(R.cochainComplexXIso 0 0 rfl).inv ≫
        (R.cochainComplex.shiftFunctorObjXIso 1 (-1) 0 (by omega)).inv)
      (show (0 : ℤ) + -1 = -1 by omega)
  refine ⟨CochainComplex.mappingCone.descHomotopy _ _ _ 0 γ ?_ ?_⟩
  · apply (Cochain.fromSingleEquiv (show (0 : ℤ) + -1 = -1 by omega)).injective
    dsimp only [Cochain.fromSingleEquiv]
    simp only [γ, Cochain.fromSingleMk_v, R.ι'_f_zero,
      CochainComplex.single₀_obj_zero, Int.reduceNeg,
      CochainComplex.shiftFunctor_obj_X', Int.reduceAdd, ShortComplex.map_X₁,
      ShortComplex.map_X₂, ShortComplex.map_f, ShortComplex.map_X₃, Cochain.ofHom_comp,
      AddEquiv.coe_mk, Equiv.coe_fn_mk, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      δ_zero, zero_add, CochainComplex.mappingCone.triangle_obj₃,
      CochainComplex.mappingCone.triangle_obj₁, Cochain.ofHom_neg, Cochain.comp_neg,
      Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.neg_v,
      CochainComplex.shiftFunctor_map_f',
      CochainComplex.mappingCone.inl_v_triangle_mor₃_f_assoc,
      CochainComplex.shiftFunctor_obj_X, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
      Category.id_comp, neg_neg, Preadditive.comp_add]
    erw [CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc
      (S.map (CochainComplex.singleFunctor C 0)) 0 (-1) (by omega)]
    simp only [zero_comp, comp_zero, Iso.inv_hom_id_assoc, Preadditive.comp_neg]
    simp [CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
  · apply (Cochain.fromSingleEquiv (show (0 : ℤ) + 0 = 0 by omega)).injective
    dsimp only [Cochain.fromSingleEquiv]
    simp only [γ, Cochain.δ_fromSingleMk, Cochain.fromSingleMk_v,
      CochainComplex.shiftFunctor_obj_X', Int.reduceAdd,
      CochainComplex.single₀_obj_zero, ShortComplex.map_X₂, ShortComplex.map_X₁,
      ShortComplex.map_f, ShortComplex.map_X₃, Cochain.ofHom_comp, AddEquiv.coe_mk,
      Equiv.coe_fn_mk, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Int.reduceNeg,
      CochainComplex.mappingCone.triangle_obj₃, CochainComplex.mappingCone.triangle_obj₁,
      Preadditive.comp_neg, CochainComplex.mappingCone.inr_triangleδ_assoc, zero_comp,
      neg_zero, Cochain.ofHom_zero, add_zero, Iso.cancel_iso_inv_left]
    erw [CochainComplex.mappingCone.inr_f_descShortComplex_f_assoc
      (S.map (CochainComplex.singleFunctor C 0)) 0]
    simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
      Cocycle.rightShift_coe, Cochain.rightShift_v _ 1 0 (zero_add 1) 0 0 (by omega) 1 rfl,
      Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.inv,
      eqToHom_refl, Category.comp_id]
    simp [S, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, R.cocomplex.toCycles_i_assoc,
      R.cochainComplex_d 0 1 0 1 rfl rfl]

/-- The cycles inclusion represents the negative of the first resolution extension.
Source: Stacks Project, Tags 06XR and 06XV; Mathlib's cone boundary is minus the projection.
(blueprint: lem-amb-first-resolution-extension-class).
Proof: the cone on G into I0 maps to the quotient cycles sheaf and to the shifted
resolution. The degree-zero identity of I0 gives a homotopy between the quotient
followed by the cycles inclusion and the negative cone boundary followed by the
augmentation. Apply the derived localization and invert the two quasi-isomorphisms. -/
theorem extMk_firstCycles :
    R.extMk (R.cocomplex.iCycles 1) 2 rfl (by simp) = -hS.extClass := by
  let := HasDerivedCategory.standard C
  let S := ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) w₀
  let S' := S.map (CochainComplex.singleFunctor C 0)
  let z := Cocycle.fromSingleMk
    (R.cocomplex.iCycles 1 ≫ (R.cochainComplexXIso 1 1 rfl).inv)
    (zero_add (1 : ℤ)) 2 rfl (by
      simp [R.cochainComplex_d 1 2 1 2 rfl rfl, Category.assoc])
  obtain ⟨H⟩ := firstBoundary_homotopy R w₀
  have he := DerivedCategory.Q_map_eq_of_homotopy C H
  apply Abelian.Ext.ext
  simp only [Abelian.Ext.neg_hom, extMk_hom,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.mk₀_id_comp, CochainComplex.singleFunctor,
    DerivedCategory.Q_obj_single_obj, Category.comp_id]
  erw [hS.extClass_hom]
  change (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q).comp
    (ShiftedHom.mk₀ 0 rfl (inv (DerivedCategory.Q.map R.ι'))) (zero_add (1 : ℤ)) = _
  rw [ShiftedHom.comp_mk₀]
  dsimp only [ShiftedHom.map]
  apply (cancel_mono ((DerivedCategory.Q.map R.ι')⟦(1 : ℤ)⟧')).1
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  let q := CochainComplex.mappingCone.descShortComplex S'
  have hq : QuasiIso q := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))
  apply (cancel_epi (DerivedCategory.Q.map q)).1
  have hδ : DerivedCategory.Q.map q ≫ hS.singleδ =
      DerivedCategory.Q.map (CochainComplex.mappingCone.triangle S'.f).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S'.X₁ := by
    dsimp only [ShortComplex.ShortExact.singleδ]
    simp only [Functor.comp_obj]
    exact DerivedCategory.descShortComplex_triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))
  conv_rhs =>
    erw [Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc, hδ,
      Category.assoc, ← (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality R.ι']
  simp only [Functor.comp_map, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  change DerivedCategory.Q.map
      (q ≫ Cocycle.equivHomShift.symm z) ≫ _ =
    -(DerivedCategory.Q.map
      ((CochainComplex.mappingCone.triangle S'.f).mor₃ ≫ R.ι'⟦(1 : ℤ)⟧') ≫ _)
  rw [he, CategoryTheory.Functor.map_neg, Preadditive.neg_comp]

end CategoryTheory.InjectiveResolution

-- Check the axioms of the completed construction.
