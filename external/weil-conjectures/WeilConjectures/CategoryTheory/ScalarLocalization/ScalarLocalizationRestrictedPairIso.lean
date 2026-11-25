/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.EqToHom

/-! # Localizing natural isomorphisms on a restricted contravariant pair domain

Source: blueprint dual-Tate compatibility, Step 5, raw coefficient transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory Opposite TensorProduct
namespace CategoryTheory.ScalarLocalization

/-- A prescribed integral comparison extends uniquely to the restricted localized pair domain.
Source: blueprint dual-Tate compatibility, Step 5
(blueprint: lem-pod-restricted-pair-localization-iso).
Proof: conjugate each localized integral component and inverse by the given object
identifications. For naturality, use the two separately additive action formulas
and induct on both tensor Hom groups. Zero and sum cases follow from additivity.
For pure tensors, both composites are integral naturality multiplied by the
product of the two scalar coefficients. The heterogeneous component identities
cancel the conjugating object equalities. Componentwise isomorphism and natural
transformation extensionality give uniqueness. No integral lifting or faithfulness
is assumed. Zero morphisms and arbitrary coefficients are included by induction. -/
theorem restrictedPairIso_existsUnique
    {R : Type*} [CommRing R] {C D : Type*}
    [Category* C] [Preadditive C] [Linear R C]
    [Category* D] [Preadditive D] [Linear R D] (t : R)
    (q : ObjectProperty (Cᵒᵖ × C))
    (q' : ObjectProperty ((ScalarLocalization R C t)ᵒᵖ × ScalarLocalization R C t))
    (hq : ∀ P, q' P → q (op P.1.unop.obj, P.2.obj))
    (U V : q.FullSubcategory ⥤ D) (α : U ≅ V)
    (F G : q'.FullSubcategory ⥤ ScalarLocalization R D t)
    (hF : ∀ P, F.obj P = ⟨U.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩⟩)
    (hG : ∀ P, G.obj P = ⟨V.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩⟩)
    (mF : ∀ P Q : q'.FullSubcategory,
      ∃ β : (Q.obj.1.unop ⟶ P.obj.1.unop) →+ (P.obj.2 ⟶ Q.obj.2) →+
          (F.obj P ⟶ F.obj Q),
        (∀ a b, F.map (ObjectProperty.homMk (Prod.mkHom a.op b)) = β a b) ∧
        ∀ a b (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b))
            ((x * y) ⊗ₜ[R] U.map (ObjectProperty.homMk
              (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩)
              (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hq _ Q.property⟩)
              (Prod.mkHom a.op b))))
    (mG : ∀ P Q : q'.FullSubcategory,
      ∃ β : (Q.obj.1.unop ⟶ P.obj.1.unop) →+ (P.obj.2 ⟶ Q.obj.2) →+
          (G.obj P ⟶ G.obj Q),
        (∀ a b, G.map (ObjectProperty.homMk (Prod.mkHom a.op b)) = β a b) ∧
        ∀ a b (x y : Localization.Away t),
          HEq (β (x ⊗ₜ[R] a) (y ⊗ₜ[R] b))
            ((x * y) ⊗ₜ[R] V.map (ObjectProperty.homMk
              (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩)
              (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hq _ Q.property⟩)
              (Prod.mkHom a.op b)))) :
    ∃! e : F ≅ G, ∀ P,
      HEq (e.hom.app P) ((ScalarLocalization.localization R D t).map
        (α.hom.app ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩)) ∧
      HEq (e.inv.app P) ((ScalarLocalization.localization R D t).map
        (α.inv.app ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩)) := by
  let Q := ScalarLocalization.localization R D t
  let I (P : q'.FullSubcategory) : q.FullSubcategory :=
    ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq _ P.property⟩
  let e (P : q'.FullSubcategory) :=
    eqToIso (hF P) ≪≫ Q.mapIso (α.app (I P)) ≪≫ (eqToIso (hG P)).symm
  have he P : HEq (e P).hom (Q.map (α.hom.app (I P))) := by
    exact (conj_eqToHom_iff_heq _ _ (hF P) (hG P)).mp rfl
  have hei P : HEq (e P).inv (Q.map (α.inv.app (I P))) := by
    apply (conj_eqToHom_iff_heq _ _ (hG P) (hF P)).mp
    change (eqToHom (hG P) ≫ Q.map (α.inv.app (I P))) ≫ eqToHom (hF P).symm = _
    exact Category.assoc _ _ _
  have hn (P P' : q'.FullSubcategory) (f : P ⟶ P') :
      F.map f ≫ (e P').hom = (e P).hom ≫ G.map f := by
    obtain ⟨β, hβ, pβ⟩ := mF P P'
    obtain ⟨γ, hγ, pγ⟩ := mG P P'
    change F.map (ObjectProperty.homMk (Prod.mkHom f.hom.1.unop.op f.hom.2)) ≫ _ =
      _ ≫ G.map (ObjectProperty.homMk (Prod.mkHom f.hom.1.unop.op f.hom.2))
    rw [hβ, hγ]
    generalize f.hom.1.unop = a, f.hom.2 = b
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [map_add, AddMonoidHom.add_apply, Preadditive.add_comp,
        Preadditive.comp_add, ha, hb]
    | tmul x a =>
      induction b using TensorProduct.inductionOn with
      | add b c hb hc =>
        simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hb, hc]
      | tmul y b =>
        have hl := heq_comp (hF P) (hF P') (hG P') (pβ a b x y) (he P')
        have hr := heq_comp (hF P) (hG P) (hG P') (he P) (pγ a b x y)
        apply eq_of_heq
        refine hl.trans (HEq.trans ?_ hr.symm)
        apply heq_of_eq
        change ScalarLocalization.composition R D t _ _ _
            (1 ⊗ₜ[R] α.hom.app (I P'))
            ((x * y) ⊗ₜ[R] U.map (ObjectProperty.homMk (Prod.mkHom a.op b))) =
          ScalarLocalization.composition R D t _ _ _
            ((x * y) ⊗ₜ[R] V.map (ObjectProperty.homMk (Prod.mkHom a.op b)))
            (1 ⊗ₜ[R] α.hom.app (I P))
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one,
          α.hom.naturality]
  refine ⟨NatIso.ofComponents e (fun f ↦ hn _ _ f), fun P ↦ ⟨he P, hei P⟩, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  exact eq_of_heq ((he' P).1.trans (he P).symm)

end CategoryTheory.ScalarLocalization
