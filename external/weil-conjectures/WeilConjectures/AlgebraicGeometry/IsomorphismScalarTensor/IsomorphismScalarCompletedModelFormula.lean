/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedFormulaChainData

/-! # Completed pure-tensor comparison

The proof applies the normalized comparison of completed-coefficient module
sheaves degreewise, then restricts the resulting natural isomorphism of complexes
to the good-complex subcategory. Its local tensor rule is exactly CompletedFormula.

## References

* Stacks Project, Tag 03EL
* Tag 0G7E
* Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4)
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

/-- Existence of the completed chain isomorphism with its normalized pure-tensor
formula. This is the comparison component of the completed model statement.
-/
theorem scalar_completed_formula
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g,
      CompletedFormula l E L ι g b := by
  obtain ⟨e, he⟩ := completed_formula_chain_data l E L ι g
  let b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g :=
    Functor.isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
      (NatIso.mapHomologicalComplex e (.up ℤ))
  refine ⟨b, ?_⟩
  intro P i U s x
  exact he (P.obj.X i) U x s

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
