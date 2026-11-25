/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceFactors
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula
import WeilConjectures.AlgebraicGeometry.RawModuleScalarHomEvaluation

/-! # The bundled scalar Hom composite

Source: Stacks Project, Tags 03FD and 03Q8, the explicit scalar map.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem map_three_factors
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z T : C} {P Q : D}
    (c : P ⟶ F.obj X) (b : F.obj T ⟶ Q)
    (m : X ⟶ Y) (z : Y ⟶ Z) (t : Z ⟶ T) (x : X ⟶ T)
    (h : x = m ≫ z ≫ t) :
    c ≫ F.map x ≫ b = c ≫ F.map m ≫ F.map z ≫ F.map t ≫ b := by
  rw [h, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
/-- Expand the scalar map on a raw module pullback, retaining all module factors.
Source: Stacks Project, Tags 03FD and 03Q8, raw-map expansion.
(blueprint: lem-sbc-raw-module-scalar-hom-composite-formula).

Proof: Evaluate rawModuleAbelianHomMap as its defining additive composite:
derived scalar forgetting on Hom groups, right composition by its coefficient
morphism b, and left composition by its source morphism c. The definitions of
scalarCoefficientFactor and scalarSourceFactor identify b and c with the displayed
factors. Apply rawModuleScalar_pullback_module_formula to the raw pullback input,
inside the derived scalar-forgetting map. This replaces that input with the
module source factor, the derived module inverse image of z, and the module
coefficient factor. Distribute scalar forgetting by Functor.map_comp,
but do not use either scalar source coherence or inverse-comparison naturality.
The equality holds for zero classes, q = 0, identity f, and zero coefficients.
-/
theorem rawModuleScalar_hom_composite_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    rawModuleAbelianHomMap Λ k G q U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (moduleCoefficientFactor Λ G (q : ℤ) A B f) ≫
      scalarCoefficientFactor Λ A.hom G (q : ℤ) := by
  exact (rawModuleScalarHom_evaluate Λ k G q U A _).trans
    (map_three_factors (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus
      (scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U))
      (scalarCoefficientFactor Λ A.hom G (q : ℤ)) _ _ _ _
      (rawModuleScalar_pullback_module_formula Λ k G q U A B f z))

end AlgebraicGeometry.Etale
