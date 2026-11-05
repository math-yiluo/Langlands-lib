import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange

/-! # Original fraction-field tensor of an actual integral closure -/

noncomputable section

universe u v w x

open scoped TensorProduct

namespace Langlands.Global

variable (A : Type u) (B : Type v) (K : Type w) (L : Type x)
  [CommRing A] [IsDomain A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra.IsAlgebraic K L]
  [Algebra A L] [IsScalarTower A K L]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-- Localization of the actual integral closure constructs its canonical generic-fiber algebra. -/
def integralClosureFractionTensorEquiv : K ⊗[A] B ≃ₐ[K] L := by
  letI : IsLocalizedModule (nonZeroDivisors A)
      (IsScalarTower.toAlgHom A B L).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr (IsIntegralClosure.isLocalization A K L B)
  letI : Algebra.IsPushout A K B L :=
    ⟨IsLocalizedModule.isBaseChange (nonZeroDivisors A) K
      (IsScalarTower.toAlgHom A B L).toLinearMap⟩
  exact Algebra.IsPushout.equiv A K B L

/-- The constructed equivalence retains both original coefficient maps. -/
@[simp]
theorem integralClosureFractionTensorEquiv_tmul (a : K) (b : B) :
    integralClosureFractionTensorEquiv A B K L (a ⊗ₜ[A] b) =
      algebraMap K L a * algebraMap B L b :=
  by
    simp [integralClosureFractionTensorEquiv, Algebra.IsPushout.equiv,
      IsBaseChange.equiv_tmul, Algebra.smul_def]

/-- The original integral-closure inclusion is the right pure-tensor map. -/
@[simp]
theorem integralClosureFractionTensorEquiv_one_tmul (b : B) :
    integralClosureFractionTensorEquiv A B K L (1 ⊗ₜ[A] b) = algebraMap B L b := by
  simp only [integralClosureFractionTensorEquiv_tmul, map_one, one_mul]

end Langlands.Global
