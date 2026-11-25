/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionConstruction
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionComplete
public import WeilConjectures.Algebra.Homology.ScalarDescent.IntegralLisseReductionScalarDescent
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientQuotients
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Finite locally free quotient towers

## References

* Bhatt--Scholze, Proposition 6.8.4(1)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale
