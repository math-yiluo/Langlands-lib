/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelFormula
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedPreservesModels

/-! # Coefficient-compatible K-flat tensor models under a scheme isomorphism

## References

* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4)
* Stacks Project, Tag 03EL
* Tag 0G7E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The completed chain comparison and preservation of flat-term K-flat models. -/
theorem scalar_completed_model
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g,
      PreservesModels l E L ι g ∧ CompletedFormula l E L ι g b := by
  obtain ⟨b, hb⟩ := scalar_completed_formula l E L ι g _hX _hY
  exact ⟨b, scalar_completed_preserves_models l E L ι g _hX _hY, hb⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
