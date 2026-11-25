/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionConstruction
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseTowerLocalBases
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionComplete
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LocalProperties

set_option linter.privateModule false

/-!
# IntegralLisseTowerEffective

## References

* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem finiteScalar_zero (n : ℕ)
    (N : ringedSiteModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (integralLisseFiniteRing l E X n))) :
    integralLisseScalar l E X ((integralLisseFiniteRestriction l E X n).obj N)
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  let := spectralNorm.normedField ℚ_[l] E
  ext U x
  have hz : (integralLisseReduction l E X n).hom.app U
      (lisseIntegerConstantSized l E X U
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) = 0 := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change _ ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ (n + 1)
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  change N.val.obj U at x
  change (integralLisseReduction l E X n).hom.app U _ • x = 0
  rw [hz, zero_smul]

private theorem towerScalar_zero (F : IntegralReductionTower l E X) (n : ℕ) :
    integralLisseScalar l E X (F.obj.obj (op n))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  obtain ⟨N, _, ⟨e⟩⟩ := F.property.1 n
  apply (cancel_epi e.hom).1
  rw [← integralLisseScalar_natural, finiteScalar_zero, zero_comp, comp_zero]

end AlgebraicGeometry.ProEtale
