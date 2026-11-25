/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousAmbientMixedCoherence
import WeilConjectures.AlgebraicGeometry.ContinuousRational.FieldChange.ContinuousMixedOrdinaryBalance
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientOperations

set_option linter.privateModule false

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-mixed-integral-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F]

private theorem scalar_normalization (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (b : FieldChange l E F i X aE aF)
    (K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) :
    b.comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        (pbcDerivedExtend b.coefficient).map (aE.integral.hom.app K) =
      aF.integral.hom.app
          ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (b.integralBalance l E F i X aE aF K.obj).hom := by
  apply (cancel_mono (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion)
    b.coefficient (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) rfl K.obj).hom).1
  simpa only [FieldChange.integralBalance, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using b.integral_normalization K

end AlgebraicGeometry.Scheme.ContinuousRational
