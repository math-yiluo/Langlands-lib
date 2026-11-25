/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor
import WeilConjectures.CategoryTheory.SectionwisePushout
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The coefficient pushout comparison

## References

* Stacks Project, Tag 03EK
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- The normalized scalar square is a pushout of ring sheaves. -/
theorem purTwistCoefficientComparison_isIso (S : Scheme.{t}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsIso (purTwistCoefficientComparison S l E) := by
  classical
  have hp : IsPushout (purTwistConstantIntegersMap S l E)
      (purTwistZlCompletionMapOfUniverses.{t, u} S l) (purTwistIntegralCompletionMap S l E)
      (purTwistCompletedScalarMap S l E) := by
    apply sheaf_isPushout_of_sectionwise (ProEt.topology S) _ _ _ _
      (purTwistCoefficientSquare S l E).symm
    intro U
    let R := (purTwistZlConstantOfUniverses.{t, u} S l).obj.obj U
    let A := (purTwistIntegralConstant S l E).obj.obj U
    let B := (purTwistZlCompletionOfUniverses.{t, u} S l).obj.obj U
    let : Algebra R A := ((purTwistConstantIntegersMap S l E).hom.app U).hom.toAlgebra
    let : Algebra R B := ((purTwistZlCompletionMapOfUniverses.{t, u} S l).hom.app U).hom.toAlgebra
    let e := (RingEquiv.ofBijective (purTwistCoefficientTensorMap S l E U)
      (purTwistCoefficientTensor S l E U)).toCommRingCatIso
    apply (CommRingCat.isPushout_tensorProduct R A B).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    · rfl
    · rfl
    · ext x
      change ((purTwistIntegralCompletionMap S l E).hom.app U) x *
        ((purTwistCompletedScalarMap S l E).hom.app U) 1 = _
      rw [map_one, mul_one]
      rfl
    · ext x
      change ((purTwistIntegralCompletionMap S l E).hom.app U) 1 *
        ((purTwistCompletedScalarMap S l E).hom.app U) x = _
      rw [map_one, one_mul]
      rfl
  have he : hp.flip.isoPushout.hom ≫ purTwistCoefficientComparison S l E = 𝟙 _ := by
    apply hp.flip.hom_ext <;> simp [purTwistCoefficientComparison]
  have h' : purTwistCoefficientComparison S l E = hp.flip.isoPushout.inv := by
    rw [← cancel_epi hp.flip.isoPushout.hom, he, Iso.hom_inv_id]
  rw [h']
  infer_instance

end AlgebraicGeometry.Scheme
