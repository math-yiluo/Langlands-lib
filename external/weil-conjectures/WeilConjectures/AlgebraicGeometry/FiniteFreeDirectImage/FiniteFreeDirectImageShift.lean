/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Shift compatibility of the canonical coefficient comparison

Source: Stacks Project, Tags 07A6 and 0DVC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

private theorem inverse_conjugate_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (δ : R₁ ⟶ R₂) [NatTrans.CommShift δ ℤ] :
    NatTrans.CommShift ((conjugateEquiv a₁ a₂).symm δ) ℤ := by
  dsimp [conjugateEquiv, mateEquiv, Iso.homCongr,
    TwoSquare.mk]
  infer_instance

private theorem restriction_shift {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S) :
    NatTrans.CommShift (proEtaleRingRestrictionDerivedDirectImage q
      R.target S.target R.source S.source a.target a.source
      R.identification S.identification a.comm).hom ℤ := by
  let ar := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let as' := proEtaleRingDerivedAdjunction q S.target S.source S.identification
  let : ar.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let : as'.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let b := proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  have hb0 : NatTrans.CommShift b.hom ℤ := by
    dsimp only [b, proEtaleRingRestrictionDerivedPullback, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := hb0
  have hb : NatTrans.CommShift b.inv ℤ := inferInstance
  let := hb
  let m := (mateEquiv as' ar (TwoSquare.mk _ _ _ _ b.inv))
  have hm : NatTrans.CommShift m ℤ := NatTrans.CommShift.mateEquiv as' ar _
  have heq : m = (proEtaleRingRestrictionDerivedDirectImage q
      R.target S.target R.source S.source a.target a.source
      R.identification S.identification a.comm).hom := by
    ext N
    have h := (proEtaleRingSheafChangeAdjunction q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).2.2
        ((proEtaleRingDerivedDirectImage q S.target S.source S.identification).obj N) N
        (as'.counit.app N)
    dsimp only [as'] at h
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
      Adjunction.right_triangle_components, CategoryTheory.Functor.map_id,
      Category.id_comp] at h
    simpa only [m, ar, as', b, mateEquiv_apply, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.id_comp,
      Category.comp_id, Category.assoc] using h
  exact heq ▸ hm

/-- The canonical scalar/direct-image mate commutes with the prescribed shifts.
Source: Stacks Project, Tags 07A6 and 0DVC.
(blueprint: lem-sp-finite-free-direct-image-shift).

Proof: restriction/pullback is induced termwise, hence commutes with shifts.
The normalized restriction/direct-image comparison is its mate under the canonical
unbounded derived adjunctions. Those adjunctions commute with shifts, as do scalar
adjunctions with their induced left shifts. Conjugation therefore gives shift
compatibility of balancing, and a second application of the mates correspondence
gives shift compatibility of comparison. -/
theorem finiteFreeDirectImageShift {Z W : Scheme.{u}} {q : Z ⟶ W}
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    {R S : Coefficients q} (a : CoefficientMap R S) :
    NatTrans.CommShift (comparison sW sZ a) ℤ := by
  let ar := proEtaleRingDerivedAdjunction q R.target R.source R.identification
  let as' := proEtaleRingDerivedAdjunction q S.target S.source S.identification
  let : ar.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let : as'.CommShift ℤ := canonicalRightDerivedAdjunctionShift _
  let : (sW.adjunction a.target).CommShift ℤ :=
    (sW.adjunction a.target).commShift_of_rightAdjoint ℤ
  let : (sZ.adjunction a.source).CommShift ℤ :=
    (sZ.adjunction a.source).commShift_of_rightAdjoint ℤ
  have hd := restriction_shift R S a
  let := hd
  have hi : NatTrans.CommShift (proEtaleRingRestrictionDerivedDirectImage q
      R.target S.target R.source S.source a.target a.source
      R.identification S.identification a.comm).inv ℤ := inferInstance
  let := hi
  have hac : (ar.comp (sZ.adjunction a.source)).CommShift ℤ := inferInstance
  have hbc : ((sW.adjunction a.target).comp as').CommShift ℤ := inferInstance
  let := hac
  let := hbc
  have hb : NatTrans.CommShift (balancing sW sZ a).hom ℤ := by
    exact inverse_conjugate_shift (ar.comp (sZ.adjunction a.source))
      ((sW.adjunction a.target).comp as') _
  let := hb
  exact NatTrans.CommShift.mateEquiv ar as' _

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
