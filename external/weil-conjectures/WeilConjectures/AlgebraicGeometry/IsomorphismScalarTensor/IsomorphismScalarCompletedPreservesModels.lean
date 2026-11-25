/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedModelBase
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import WeilConjectures.AlgebraicGeometry.IsomorphismScalarTensor.IsomorphismScalarCompletedPreservesModelsInverse

/-! # Preservation of completed flat-term K-flat models

The proof applies the isomorphism-of-sites ringed-topos pullback theorem to the
transported inverse image, then applies the identity and completed scalar
extension instances to the three complexes in PreservesModels. The argument is
termwise and remains valid for unbounded, zero, and empty-site complexes.

## References

* Stacks Project, Tags 03EL and 06YY
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

/-- Preservation of the three completed flat-term K-flat model clauses. -/
theorem scalar_completed_preserves_models
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    PreservesModels l E L ι g := by
  intro P
  obtain ⟨_hprodY, hscalarY, _hcounitY⟩ :=
    finiteFreeScalarCochainProperties l E L ι Y
  obtain ⟨_hprodX, hscalarX, _hcounitX⟩ :=
    finiteFreeScalarCochainProperties l E L ι X
  have hinv := inverseImageIntegralModules_preserves_good l E g P
  exact ⟨hinv, hscalarY P, hscalarX ⟨(inverseComplex l E g).obj P.obj, hinv⟩⟩

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
