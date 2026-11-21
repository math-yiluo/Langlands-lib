import Langlands.Global.Arithmetic.HarrisProposition48ParityReductionStatement

/-! # Conditional auxiliary determinant untwisting for Harris Proposition 4.8 -/

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic
open AdelicFunctoriality (ideleClassNorm)
open CuspidalOperatorRealization.IsoClass
  (isWeakAutomorphicInductionOf_iff hasSupercuspidalComponent_iff)
open ContinuousRationalFunctions (evaluate determinantMultiplier evaluate_determinantMultiplier)

set_option maxHeartbeats 500000 in
/-- The inverse of the actual `ν⁻¹` twist equivalence multiplies functions by `ν ∘ det`. -/
private theorem inverseTwist_isDeterminantMultiple {E : Type} [Field E] [NumberField E]
    {n : ℕ} (T : OperatorRealization E n) (ν : HeckeCharacter E) :
    OperatorRealization.IsDeterminantMultiple ν (T.heckeDeterminantTwist ν⁻¹) T := by
  let e := (T.heckeDeterminantTwistEquiv ν⁻¹).toLinearEquiv
  refine ⟨e.symm, ?_⟩
  intro f
  obtain ⟨f, rfl⟩ := e.surjective f
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change evaluate E n (T.toContinuous f) g =
    evaluate E n (determinantMultiplier n ν
      ((T.heckeDeterminantTwist ν⁻¹).toContinuous (T.heckeDeterminantTwistEquiv ν⁻¹ f))) g
  rw [evaluate_determinantMultiplier, OperatorRealization.evaluate_heckeDeterminantTwistEquiv,
    HeckeCharacter.adelicDeterminant_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_mul]

/-- The three twist compatibilities give the auxiliary untwist on actual realizations. -/
theorem proposition48AuxiliaryParityUntwistReduction :
    Proposition48AuxiliaryParityUntwistReductionStatement.{uF, uV} := by
  intro hWeakTwist hDualTwist hSuperTwist Q b ν χs _ hNormalization r c hCorrected
  obtain ⟨T, rfl⟩ := c.exists_representative
  obtain ⟨hWeak, hAlg, hDual, hSuper⟩ := hCorrected
  let S := T.heckeDeterminantTwist ν⁻¹
  have hWeakS : S.isoClass.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ := by
    obtain ⟨P, hP⟩ := (isWeakAutomorphicInductionOf_iff.{0, 0, uV}
      T (Q.correctedCharacter ν)).mp hWeak
    have hCancel : Q.correctedCharacter ν * HeckeCharacter.normComp (L := Q.E') ν⁻¹ = Q.ξ := by
      apply ContinuousMonoidHom.ext
      intro x
      change (Q.ξ x * ν (ideleClassNorm (K := Q.E) (L := Q.E') x)) *
        (ν (ideleClassNorm (K := Q.E) (L := Q.E') x))⁻¹ = Q.ξ x
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have hP' := hWeakTwist Q.E Q.E' T P (Q.correctedCharacter ν) ν⁻¹ hP
    rw [hCancel] at hP'
    exact (isWeakAutomorphicInductionOf_iff.{0, 0, uV} S Q.ξ).mpr
      ⟨P.heckeDeterminantTwist ν⁻¹, hP'⟩
  have hDualS : S.isoClass.IsConjugateSelfDual := by
    have hν : ν.complexConj = ν⁻¹ := ContinuousMonoidHom.ext hNormalization.1
    have hInv : ν⁻¹.complexConj = (ν⁻¹)⁻¹ := by
      rw [HeckeCharacter.complexConj_inv, hν]
    exact S.isoClass_isConjugateSelfDual_iff.mpr
      (hDualTwist Q.E T.realization ν⁻¹ hInv (T.isoClass_isConjugateSelfDual_iff.mp hDual))
  have hSuperS : S.isoClass.HasSupercuspidalComponent.{0, uV} Q.Ps.v := by
    obtain ⟨P, hP⟩ := (hasSupercuspidalComponent_iff.{0, uV} T Q.Ps.v).mp hSuper
    exact (hasSupercuspidalComponent_iff.{0, uV} S Q.Ps.v).mpr
      ⟨P.heckeDeterminantTwist ν⁻¹, hSuperTwist Q.E T P ν⁻¹ Q.Ps.v hP⟩
  refine ⟨S, T, rfl, hWeakS, hDualS, hSuperS, hWeak, hAlg, hDual, hSuper, ?_⟩
  exact inverseTwist_isDeterminantMultiple T.realization ν

end Langlands.Global.Harris
