/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseFiniteConstants
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientQuotients
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseLocalization
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionNormalized
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseTowerEffective

/-!
# Integral lisse modules and their normalized reduction towers

The finite coefficient sheaves are first presented as continuous functions into the quotient
rings, with their quotient topology. The statement identifies these with constant sheaves.
Towers are written in the integral module category by restriction of scalars. Normalization
is the cokernel universal property for multiplication by the relevant power of the uniformizer;
this is precisely the induced sheaf tensor quotient, not invertibility of the transition itself.

## References

* Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(1), pp. 58--59
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

end AlgebraicGeometry.ProEtale
