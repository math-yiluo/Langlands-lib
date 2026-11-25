/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteCore
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteSquares

/-! # Finite scalar tensor comparisons in the specified cochain presentations

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

/-- The finite comparisons, canonical quotient maps and adjacent transition maps
for a supplied normalized completed chain comparison. -/
theorem scalar_finite_model
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
    QuotientSquare l E L ι g b bfin vleft vright ∧
    LeftTransitionFormula l E L ι g tleft ∧
    RightTransitionFormula l E L ι g tright ∧
    TransitionSquare l E L ι g bfin tleft tright := by
  obtain ⟨bfin, vleft, vright, tleft, tright, hF, hL, hR, hTL, hTR⟩ :=
    scalar_finite_core l E L ι g b hb
  obtain ⟨hQ, hT⟩ := scalar_finite_squares l E L ι g b bfin vleft vright tleft tright
    hb hF hL hR hTL hTR
  exact ⟨bfin, vleft, vright, tleft, tright, hF, hL, hR, hQ, hTL, hTR, hT⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
