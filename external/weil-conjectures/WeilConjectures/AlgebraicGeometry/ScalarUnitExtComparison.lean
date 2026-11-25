/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB uD uE vC vB vD vE wC wB wD wE
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Abelian.Ext
variable {C : Type uC} {B : Type uB} {D : Type uD} {E : Type uE}
  [Category.{vC} C] [Category.{vB} B] [Category.{vD} D] [Category.{vE} E]
  [Abelian C] [Abelian B] [Abelian D] [Abelian E]
  [HasExt.{wC} C] [HasExt.{wB} B] [HasExt.{wD} D] [HasExt.{wE} E]
  (F : C ⥤ D) (G : B ⥤ E) (U : C ⥤ B) (V : D ⥤ E)
  [F.Additive] [G.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem mapExactFunctor_square (τ : U ⋙ G ≅ F ⋙ V) {P Q : C} {n : ℕ}
    (c : Ext.{wC} P Q n) :
    ((c.mapExactFunctor U).mapExactFunctor G).comp (mk₀ (τ.hom.app Q)) (add_zero n) =
      (mk₀ (τ.hom.app P)).comp
        ((c.mapExactFunctor F).mapExactFunctor V) (zero_add n) := by
  have hc := mapExactFunctor_comp_mk₀_eq_sheaf U G (U ⋙ G) (Iso.refl _) c
  simp only [Iso.refl_hom, NatTrans.id_app, comp_mk₀_id, mk₀_id_comp] at hc
  rw [← hc]
  exact mapExactFunctor_comp_mk₀_eq_sheaf F V (U ⋙ G) τ c
private theorem precomp_bijective {P P' Q : C} (a : P ≅ P') (n : ℕ) :
    Function.Bijective (fun c : Ext.{wC} P' Q n ↦
      (mk₀ a.hom).comp c (zero_add n)) := by
  let e : Ext.{wC} P' Q n ≃ Ext.{wC} P Q n :=
    { toFun := fun c ↦ (mk₀ a.hom).comp c (zero_add n)
      invFun := fun c ↦ (mk₀ a.inv).comp c (zero_add n)
      left_inv := by
        intro c
        simp only [mk₀_comp_mk₀_assoc, Iso.inv_hom_id, mk₀_id_comp]
      right_inv := by
        intro c
        simp only [mk₀_comp_mk₀_assoc, Iso.hom_inv_id, mk₀_id_comp] }
  exact e.bijective

private theorem postcomp_bijective {P Q Q' : C} (a : Q ≅ Q') (n : ℕ) :
    Function.Bijective (fun c : Ext.{wC} P Q n ↦
      c.comp (mk₀ a.hom) (add_zero n)) := by
  let e : Ext.{wC} P Q n ≃ Ext.{wC} P Q' n :=
    { toFun := fun c ↦ c.comp (mk₀ a.hom) (add_zero n)
      invFun := fun c ↦ c.comp (mk₀ a.inv) (add_zero n)
      left_inv := by
        intro c
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, Iso.hom_inv_id, comp_mk₀_id]
      right_inv := by
        intro c
        simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, Iso.inv_hom_id, comp_mk₀_id] }
  exact e.bijective

/-- In an exact-functor square U⋙G≅F⋙V between abelian categories, assume F and G induce bijections
on Ext, and the degree-n Ext map induced by a specified scalar unit η is bijective. After
transporting its source and target by specified isomorphisms, the corresponding V-scalar-unit map on
Ext is also bijective [def-weil-abstract-derived-category].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: Naturality of exact-functor Ext maps for the square isomorphism makes the two maps a
commuting square after the endpoint isomorphisms. Those isomorphisms induce bijections by Yoneda
composition, as do F and G by assumption. Express the lower map as a composite of these bijections
and the inverse of the upper comparison; its bijectivity follows. -/
theorem scalar_unit_ext_comparison_bijective
    (τ : U ⋙ G ≅ F ⋙ V) {P Q : C} {X : B} {X' : E} {P' : D}
    (η : X ⟶ U.obj P) (s : G.obj X ≅ X') (a : F.obj P ≅ P') (n : ℕ)
    (hU : Function.Bijective (fun c : Ext.{wC} P Q n ↦
      (mk₀ η).comp (c.mapExactFunctor U) (zero_add n)))
    (hF : Function.Bijective (fun c : Ext.{wC} P Q n ↦ c.mapExactFunctor F))
    (hG : Function.Bijective (fun c : Ext.{wB} X (U.obj Q) n ↦
      c.mapExactFunctor G)) :
    Function.Bijective (fun c : Ext.{wD} P' (F.obj Q) n ↦
      (mk₀ (s.inv ≫ G.map η ≫ τ.hom.app P ≫ V.map a.hom)).comp
        (c.mapExactFunctor V) (zero_add n)) := by
  have hl := (precomp_bijective a.symm n (Q := F.obj Q)).comp hF
  have hr := (precomp_bijective s.symm n (Q := V.obj (F.obj Q))).comp
    ((postcomp_bijective (τ.app Q) n (P := G.obj X)).comp hG)
  have hb := hr.comp hU
  have he (c : Ext.{wC} P Q n) :
      (mk₀ (s.inv ≫ G.map η ≫ τ.hom.app P ≫ V.map a.hom)).comp
          (((mk₀ a.inv).comp (c.mapExactFunctor F) (zero_add n)).mapExactFunctor V)
          (zero_add n) =
        (mk₀ s.inv).comp
          ((((mk₀ η).comp (c.mapExactFunctor U) (zero_add n)).mapExactFunctor G).comp
            (mk₀ (τ.hom.app Q)) (add_zero n)) (zero_add n) := by
    rw [mapExactFunctor_comp, mapExactFunctor_mk₀, mk₀_comp_mk₀_assoc]
    have hη : (s.inv ≫ G.map η ≫ τ.hom.app P ≫ V.map a.hom) ≫ V.map a.inv =
        s.inv ≫ G.map η ≫ τ.hom.app P := by
      simp only [Category.assoc, ← V.map_comp, Iso.hom_inv_id, V.map_id]
      erw [Category.comp_id]
    rw [hη]
    simp only [mapExactFunctor_comp, mapExactFunctor_mk₀,
      comp_assoc_of_third_deg_zero]
    rw [mapExactFunctor_square F G U V τ c]
    simp only [mk₀_comp_mk₀_assoc]
  apply (Function.Bijective.of_comp_iff _ hl).mp
  simpa only [Function.comp_def, Iso.symm_hom, Iso.app_hom, he] using hb

end CategoryTheory.Abelian.Ext
