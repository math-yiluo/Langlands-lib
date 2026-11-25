/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionResolution
import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionCochainModel
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Localization of the arithmetic cochain comparison

Source: Stacks Project, Tags 0941 and 0H9K.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe a b w uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic

private lemma productCone
    {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] (T : ℕ → CochainComplex A ℤ)
    [∀ n : ℕ, (T n).IsKInjective] :
    Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor T)))) := by
  obtain ⟨_, h⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit T
  have : PreservesLimit (Discrete.functor T) DerivedCategory.Q :=
    preservesLimit_of_preserves_limit_cone
      (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor T)) h.some
  exact ⟨isLimitOfPreserves DerivedCategory.Q (limit.isLimit _)⟩

end CategoryTheory.StrictTowerArithmetic
