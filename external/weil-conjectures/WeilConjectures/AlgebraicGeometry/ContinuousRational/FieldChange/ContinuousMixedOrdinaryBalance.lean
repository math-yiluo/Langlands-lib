/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousAmbientMixedCoherence

/-! # The mixed balancing cube before completion

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]

/-- Flatten integral scalar extension and then insert the rational coefficient factor.
This is a specified pair of derived tensor associators, independent of the realization.
Source: BS 6.8.14--6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-mixed-ordinary-balance). -/
def FieldChange.integralBalance (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (b : FieldChange l E F i X aE aF)
    (K : PbcCompletedDerived X.scheme (pbcIntegralDatum l E)) :
    (pbcDerivedExtend (aF.integralIso.hom ≫ aF.inclusion)).obj
        ((pbcEmbeddingAmbientTensor l E F i X.scheme).obj K) ≅
      (pbcDerivedExtend b.coefficient).obj
        ((pbcDerivedExtend (aE.integralIso.hom ≫ aE.inclusion)).obj K) :=
  pbcReductionNormalization (pbcScalarCoefficientMap l E F i X.scheme)
      (aF.integralIso.hom ≫ aF.inclusion)
      (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) b.square K ≪≫
    (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion) b.coefficient
      (aE.integralIso.hom ≫ aE.inclusion ≫ b.coefficient) rfl K).symm

end AlgebraicGeometry.Scheme.ContinuousRational
