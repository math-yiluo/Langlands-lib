/-
This file belongs to the Library. It states two theorems of the NYLL library with the fields as
explicit arguments and proves them by NYLL's own theorems. NYLL
(https://github.com/n-yamaguchi-0729/NYLL) is Copyright (c) 2026 Naganori Yamaguchi and released
under the Apache License, Version 2.0; its licence and notice are in `licenses/NYLL/`.
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure

/-! # NYLL integral-closure theorems with explicit field arguments -/

open ValuationTheory.DiscreteValuationField

universe u v w

namespace Langlands.CommutativeAlgebra.FiniteIntegralClosure

theorem integralClosure_isDiscreteValuationRing_of_finite_separable
    (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing (integralClosure base.valuationSubring L) :=
  ValuedExtension.integralClosure_isDiscreteValuationRing_of_finite_separable
    (K := K) (L := L) base

theorem integralClosure_maximalIdeal_isAdicComplete_of_finite_separable
    (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L] :
    IsAdicComplete (ValuedExtension.CanonicalIntegralClosure.maximalIdeal (L := L) base)
      (integralClosure base.valuationSubring L) :=
  ValuedExtension.integralClosure_maximalIdeal_isAdicComplete_of_finite_separable
    (K := K) (L := L) base

end Langlands.CommutativeAlgebra.FiniteIntegralClosure
