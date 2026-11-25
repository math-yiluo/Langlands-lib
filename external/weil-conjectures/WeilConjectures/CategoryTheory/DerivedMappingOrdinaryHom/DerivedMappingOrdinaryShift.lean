/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedMappingOrdinaryHom.DerivedMappingOrdinaryHom
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # The signed target shift of the ordinary linear Hom complex

Source: Stacks Project, Differential Graded Algebra, Example 09L9.
(blueprint: lem-sf-derived-mapping-ordinary-shift)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u

open CategoryTheory CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingOrdinaryHom

variable (B : Type b) [CommRing B]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear B A]

/-- The family identification underlying the shift of the Hom complex.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-shift). -/
def shiftLinearEquiv (X Y : CochainComplex A ℤ) (a n : ℤ) :
    ULift.{b} (Cochain X (Y⟦a⟧) n) ≃ₗ[ULift.{v} B]
      ULift.{b} (Cochain X Y (n + a)) where
  toFun x := ULift.up (x.down.rightUnshift (n + a) rfl)
  invFun x := ULift.up (x.down.rightShift a n rfl)
  left_inv x := by apply ULift.ext; simp
  right_inv x := by apply ULift.ext; simp
  map_add' x y := by apply ULift.ext; simp
  map_smul' a x := by apply ULift.ext; simp

/-- The target-shift isomorphism of unbounded linear Hom complexes.
The factor in the shifted differential cancels the factor in `δ_rightUnshift`.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-shift). -/
def targetShift (X Y : CochainComplex A ℤ) (a : ℤ) :
    complex B X (Y⟦a⟧) ≅ (complex B X Y)⟦a⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (shiftLinearEquiv B X Y a n).toModuleIso) (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply ULift.ext
      change a.negOnePow • δ (n + a) (m + a) (x.down.rightUnshift (n + a) rfl) =
        (δ n m x.down).rightUnshift (m + a) rfl
      rw [Cochain.δ_rightUnshift _ (n + a) rfl (m + a) m rfl]
      simp only [smul_smul, Int.units_mul_self, one_smul])

/-- On families of morphisms, the shift is precisely Mathlib's `rightUnshift`.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-shift).
Proof: evaluate the component isomorphism; the degree-reindexing isomorphism is the identity. -/
theorem targetShift_apply (X Y : CochainComplex A ℤ) (a n : ℤ)
    (x : (complex B X (Y⟦a⟧)).X n) :
    (((complex B X Y).shiftFunctorObjXIso a n (n + a) rfl).hom
      ((targetShift B X Y a).hom.f n x)).down =
        x.down.rightUnshift (n + a) rfl := by
  rfl

end CategoryTheory.DerivedMappingOrdinaryHom
