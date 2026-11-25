/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModel
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteLeftQuotientFormula
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarFiniteRightQuotientFormula

/-! # Finite scalar quotient formulas

This is the quotient-map component of the finite scalar model.  It is split
from the finite comparison and transition constructions.

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
The two canonical maps from the completed scalar complexes to their finite
restrictions exist and satisfy their local quotient formulas.
-/
theorem quotient_formulas_exists
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
    ∃ vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n,
      LeftQuotientFormula l E L ι g vleft ∧
    ∃ vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n,
      RightQuotientFormula l E L ι g vright := by
  obtain ⟨vleft, hleft⟩ := left_quotient_formula_exists l E L ι g b hb
  obtain ⟨vright, hright⟩ := right_quotient_formula_exists l E L ι g b hb
  exact ⟨vleft, hleft, vright, hright⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
