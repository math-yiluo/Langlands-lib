/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionConstruction
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientQuotients
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LocalProperties

set_option linter.privateModule false

/-!
# IntegralLisseReductionComplete

## References

* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private abbrev finiteUnit (n : ℕ) :=
  (integralLisseFiniteRestriction l E X n).obj
    (SheafOfModules.unit ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (integralLisseFiniteRing l E X n)))

end AlgebraicGeometry.ProEtale
