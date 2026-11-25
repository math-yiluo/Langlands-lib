/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteComparisonFormula
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteQuotientFormulas
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteTransitionFormulas

/-! # Finite scalar comparison and reduction formulas

This is the finite formula portion of the finite scalar model. It records the
finite comparison, quotient maps, and transition maps together with their local
formulas. The two categorical commutative squares are isolated in
`IsomorphismScalarFiniteSquares`.

## References

* Stacks Project, Tags 03EK and 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/--
Finite comparisons and local quotient/transition formulas can be constructed from
a normalized completed comparison. This is Steps 1--6 of the finite coefficient
calculation in Stacks 03EK and 03EL; the categorical square equalities are the
separate conclusion of `scalar_finite_squares`.
-/
theorem scalar_finite_core
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
      (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
      (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
      (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n),
    FiniteFormula l E L ι g bfin ∧
    LeftQuotientFormula l E L ι g vleft ∧
    RightQuotientFormula l E L ι g vright ∧
    LeftTransitionFormula l E L ι g tleft ∧
    RightTransitionFormula l E L ι g tright := by
  obtain ⟨bfin, hF⟩ := finite_formula_exists l E L ι g b hb
  obtain ⟨vleft, hL, vright, hR⟩ := quotient_formulas_exists l E L ι g b hb
  obtain ⟨tleft, hTL, tright, hTR⟩ := transition_formulas_exists l E L ι g b hb
  exact ⟨bfin, vleft, vright, tleft, tright, hF, hL, hR, hTL, hTR⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
