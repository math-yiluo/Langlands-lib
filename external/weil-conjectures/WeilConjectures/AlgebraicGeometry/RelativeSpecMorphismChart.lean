/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
@[expose] public section
universe u
open CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry
/-- The local chart compatibility for the relative-spectrum anti-equivalence, provided
its forward functor acts on morphisms by the canonical section maps (`hmap`).
Source: Stacks Project, Morphisms, Lemma 01SA and Constructions, Lemma 01LX
(blueprint: lem-weil-pbc-relative-spec-morphism-chart).

Proof: Apply naturality of the counit of the equivalence to an algebra morphism,
then use the affine `toSpecΓ` naturality lemma and functoriality of `Spec.map`. -/
theorem relative_spec_morphism_chart (S : Scheme.{u})
    (E : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
    (hobj : ∀ Y, (E.functor.obj (op Y)).obj = Under.mk (⟨Y.obj.hom.c⟩ : Scheme.sheaf _ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} Y.obj.hom.base).obj (Scheme.sheaf _)))
    (hmap : ∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
      (E.functor.map h.op).hom.right.hom.app (op V) =
        eqToHom (by rw [hobj Y']; rfl) ≫
          h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
            (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
          eqToHom (by rw [hobj Y]; rfl))
    : ∀ (A B) (φ : A ⟶ B) (U : S.Opens), IsAffineOpen U →
      (E.inverse.map φ).unop.hom.left.resLE ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U)
          ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, Over.w (E.inverse.map φ).unop.hom]) ≫
        ((E.inverse.obj A).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
        Spec.map (((E.counitIso.app A).inv.hom ≫
          eqToHom (hobj (E.inverse.obj A).unop)).right.hom.app (op U)) =
      ((E.inverse.obj B).unop.obj.hom ⁻¹ᵁ U).toSpecΓ ≫
        Spec.map (((E.counitIso.app B).inv.hom ≫
          eqToHom (hobj (E.inverse.obj B).unop)).right.hom.app (op U)) ≫
        Spec.map (φ.hom.right.hom.app (op U)) := by
  intro A B φ U hU
  have htransport {C D : TopCat.Sheaf CommRingCat.{u} S}
      (e : C = D) : (eqToHom e).hom.app (op U) =
        eqToHom (congrArg (fun F ↦ F.obj.obj (op U)) e) :=
    (congrArg (fun f ↦ f.app (op U))
      (eqToHom_map (TopCat.Sheaf.forget CommRingCat.{u} S) e)).trans
        (eqToHom_app _ (op U))
  simp only [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  simp only [← Spec.map_comp]
  congr 1
  congr 1
  have hn := congrArg (fun t ↦ t.hom.right.hom.app (op U))
    (E.counitIso.inv.naturality φ)
  have hm := hmap (E.inverse.obj B).unop (E.inverse.obj A).unop
    (E.inverse.map φ).unop U
  simp only [Quiver.Hom.op_unop] at hm
  simp only [Functor.id_map, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
    Under.comp_right, TopCat.Sheaf.comp_app] at hn
  simp only [hm] at hn
  simp only [Under.comp_right, Under.eqToHom_right, TopCat.Sheaf.comp_app,
    htransport, Category.assoc] at hn ⊢
  have ht := congrArg (· ≫ eqToHom
    (congrArg (fun C : S.CommAlgebraSheaf ↦ C.right.obj.obj (op U))
      (hobj (E.inverse.obj B).unop))) hn
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at ht
  exact ht.symm
end AlgebraicGeometry
