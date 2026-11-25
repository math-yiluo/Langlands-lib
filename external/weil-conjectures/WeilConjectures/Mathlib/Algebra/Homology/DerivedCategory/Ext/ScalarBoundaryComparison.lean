/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
/-! # Comparison of scalar adjunct boundary equations
(blueprint: lem-sp-scalar-boundary-comparison).
-/

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

/-- In an exact-functor square U⋙G≅F⋙V, a degree-two class c with scalar adjunct βκ transports to
the class d under given source comparison isomorphisms. If the degree-one Kummer classes κ and
κprime commute with the target comparison and with a map on unit sheaves, then the V-scalar adjunct
of d is the transported boundary composed with κprime [def-weil-abstract-derived-category].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-scalar-boundary-comparison).
Proof: Apply the exact comparison functor to the scalar-adjunct equation. Use the square isomorphism
naturality on Ext, the source comparison identity and the Kummer compatibility. Reassociate Yoneda
products and cancel the invertible source map. The remaining terms are exactly the transported
source generator and boundary; no faithfulness of forgetting scalars is used. -/
theorem scalar_boundary_comparison
    (τ : U ⋙ G ≅ F ⋙ V) {P Q : C} {X Y : B} {X' Y' : E} {P' : D}
    (η : X ⟶ U.obj P) (s : G.obj X ≅ X') (a : F.obj P ≅ P')
    (b : G.obj Y ⟶ Y') (β : Ext.{wB} X Y 1) (κ : Ext.{wB} Y (U.obj Q) 1)
    (κ' : Ext.{wE} Y' (V.obj (F.obj Q)) 1)
    (c : Ext.{wC} P Q 2) (d : Ext.{wD} P' (F.obj Q) 2)
    (hc : (mk₀ η).comp (c.mapExactFunctor U) (zero_add 2) = β.comp κ rfl)
    (hd : (mk₀ a.hom).comp d (zero_add 2) = c.mapExactFunctor F)
    (hκ : (mk₀ b).comp κ' (zero_add 1) =
      (κ.mapExactFunctor G).comp (mk₀ (τ.hom.app Q)) (add_zero 1)) :
    (mk₀ (s.inv ≫ G.map η ≫ τ.hom.app P ≫ V.map a.hom)).comp
        (d.mapExactFunctor V) (zero_add 2) =
      ((mk₀ s.inv).comp
        ((β.mapExactFunctor G).comp (mk₀ b) (add_zero 1)) (zero_add 1)).comp κ' rfl := by
  have hs := mapExactFunctor_square F G U V τ c
  have hη : (mk₀ (s.inv ≫ G.map η ≫ τ.hom.app P ≫ V.map a.hom)).comp
        (d.mapExactFunctor V) (zero_add 2) =
      (mk₀ s.inv).comp
        (((mk₀ η).comp (c.mapExactFunctor U) (zero_add 2)).mapExactFunctor G |>.comp
          (mk₀ (τ.hom.app Q)) (add_zero 2)) (zero_add 2) := by
    simp only [mapExactFunctor_comp, mapExactFunctor_mk₀,
      comp_assoc_of_third_deg_zero]
    rw [hs]
    simp only [mk₀_comp_mk₀_assoc]
    rw [← hd, mapExactFunctor_comp, mapExactFunctor_mk₀]
    simp only [mk₀_comp_mk₀_assoc]
    simp only [Category.assoc]
  rw [hη, hc, mapExactFunctor_comp]
  rw [comp_assoc (β.mapExactFunctor G) (κ.mapExactFunctor G)
    (mk₀ (τ.hom.app Q)) rfl (add_zero 1) (add_zero 2)]
  rw [← hκ]
  rw [← comp_assoc (β.mapExactFunctor G) (mk₀ b) κ'
    (add_zero 1) (zero_add 1) rfl]
  rw [comp_assoc (mk₀ s.inv) ((β.mapExactFunctor G).comp (mk₀ b) (add_zero 1)) κ'
    (zero_add 1) rfl rfl]

end CategoryTheory.Abelian.Ext
