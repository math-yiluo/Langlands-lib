import Langlands.Representation.Plancherel.LeviNormalizedProductCoefficients

/-! # Forward tensors with the inverse of the reverse induced dual operator -/

noncomputable section

open Langlands.Aubert.General
open scoped TensorProduct

set_option maxRecDepth 2048

namespace Langlands.Plancherel

universe uG uA uB

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U Q N V : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N V)
  (hU : IsClosed (U : Set G)) (hV : IsClosed (V : Set G))
  (A : SmoothRep.{0, uG, uA} ℂ M) (B : SmoothRep.{0, uG, uB} ℂ N)
  (J : ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.IntertwiningMap
    ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B).representation)
  (R : ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B.contragredient).representation.IntertwiningMap
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient).representation)
  (hR : Function.Bijective R)

/-- Invert this particular reverse operator on the induced smooth dual. -/
def reverseInducedDualInverse :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient).representation.IntertwiningMap
      ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B.contragredient).representation :=
  (R.ofBijective hR).symm.toIntertwiningMap

/-- The inverse is a right inverse of the supplied reverse operator itself. -/
@[simp]
theorem reverseInducedDualInverse_apply
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    R (reverseInducedDualInverse h k hU hV A B R hR ℓ) = ℓ :=
  (R.ofBijective hR).apply_symm_apply ℓ

/-- The inverse is also a left inverse of that same operator. -/
@[simp]
theorem reverseInducedDualInverse_apply_reverse
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor k hV).obj B.contragredient) :
    reverseInducedDualInverse h k hU hV A B R hR (R ℓ) = ℓ :=
  (R.ofBijective hR).symm_apply_apply ℓ

include hR in
/-- Nonzero scalar rescaling preserves bijectivity of this reverse operator. -/
theorem reverseInducedDual_rescale_bijective (c : ℂ) (hc : c ≠ 0) :
    Function.Bijective (c • R) :=
  (LinearEquiv.smulOfNeZero ℂ _ c hc).bijective.comp hR

/-- The inverse of the rescaled reverse operator has reciprocal scale. -/
theorem reverseInducedDualInverse_rescale (c : ℂ) (hc : c ≠ 0)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    reverseInducedDualInverse h k hU hV A B (c • R)
        (reverseInducedDual_rescale_bijective h k hU hV A B R hR c hc) ℓ =
      c⁻¹ • reverseInducedDualInverse h k hU hV A B R hR ℓ := by
  apply (reverseInducedDual_rescale_bijective h k hU hV A B R hR c hc).injective
  rw [reverseInducedDualInverse_apply]
  change ℓ = c • R (c⁻¹ • reverseInducedDualInverse h k hU hV A B R hR ℓ)
  rw [map_smul, reverseInducedDualInverse_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Tensor a forward induced intertwiner with the inverse of the reverse
induced dual intertwiner, for the two actual external actions. -/
def reverseDualTensorIntertwiner :
    (Induction.BinaryTensor.external
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient).representation).IntertwiningMap
    (Induction.BinaryTensor.external
      ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B).representation
      ((DynamicNormalization.leviTwistedInductionFunctor k hV).obj B.contragredient).representation) where
  toLinearMap := TensorProduct.map J.toLinearMap
    (reverseInducedDualInverse h k hU hV A B R hR).toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul f ℓ =>
      change J (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
          x.1 f) ⊗ₜ[ℂ]
          reverseInducedDualInverse h k hU hV A B R hR
            (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient).representation
              x.2 ℓ) = _
      rw [J.isIntertwining,
        (reverseInducedDualInverse h k hU hV A B R hR).isIntertwining]
      rfl
    | add t s ht hs => simp only [LinearMap.comp_apply, map_add, ht, hs]

@[simp]
theorem reverseDualTensorIntertwiner_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    reverseDualTensorIntertwiner h k hU hV A B J R hR (f ⊗ₜ[ℂ] ℓ) =
      J f ⊗ₜ[ℂ] reverseInducedDualInverse h k hU hV A B R hR ℓ := rfl

/-- A common nonzero scalar on the forward and reverse dual operators
cancels in their specified tensor. -/
theorem reverseDualTensorIntertwiner_rescale (c : ℂ) (hc : c ≠ 0) :
    reverseDualTensorIntertwiner h k hU hV A B (c • J) (c • R)
        (reverseInducedDual_rescale_bijective h k hU hV A B R hR c hc) =
      reverseDualTensorIntertwiner h k hU hV A B J R hR := by
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext
  ext f ℓ
  change (c • J f) ⊗ₜ[ℂ]
    reverseInducedDualInverse h k hU hV A B (c • R)
      (reverseInducedDual_rescale_bijective h k hU hV A B R hR c hc) ℓ =
        J f ⊗ₜ[ℂ] reverseInducedDualInverse h k hU hV A B R hR ℓ
  rw [reverseInducedDualInverse_rescale h k hU hV A B R hR c hc,
    TensorProduct.smul_tmul_smul,
    mul_inv_cancel₀ hc, one_smul]

variable [SecondCountableTopology G]
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient Q)]
  (huni : IsUnimodularModulus U hU) (hvni : IsUnimodularModulus V hV)

/-- The algebraic forward/reverse-dual tensor on the actual positive-Levi
product coefficient carriers. The inputs remain explicit intertwiners. -/
def reverseDualTensorComparison :
    (leviProductInducedCoefficientObject h hU A).representation.IntertwiningMap
      (leviProductInducedCoefficientObject k hV B).representation :=
  ((leviNormalizedProductInductionTensorEquiv k k hV hV hvni hvni B B.contragredient).toIntertwiningMap.comp
    (reverseDualTensorIntertwiner h k hU hV A B J R hR)).comp
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient).symm.toIntertwiningMap

/-- This tensor has exactly the forward/inverse-reverse-dual formula. -/
@[simp]
theorem reverseDualTensorComparison_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    reverseDualTensorComparison h k hU hV A B J R hR huni hvni
        (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
          (f ⊗ₜ[ℂ] ℓ)) =
      leviNormalizedProductInductionTensorEquiv k k hV hV hvni hvni B B.contragredient
        (J f ⊗ₜ[ℂ] reverseInducedDualInverse h k hU hV A B R hR ℓ) := by
  change leviNormalizedProductInductionTensorEquiv k k hV hV hvni hvni B B.contragredient
    (reverseDualTensorIntertwiner h k hU hV A B J R hR
      ((leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient).symm
        (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
          (f ⊗ₜ[ℂ] ℓ)))) = _
  rw [Representation.Equiv.symm_apply_apply]
  rfl

/-- Evaluation is the pointwise tensor of the specified two induced operators. -/
theorem reverseDualTensorComparison_tmul_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient)
    (x : G × G) :
    Induction.eval (Q.prod Q)
        (leviInflatedInducingRepresentation (k.prod k) (hV.prod hV)
          (productLeviObject B B.contragredient))
        (reverseDualTensorComparison h k hU hV A B J R hR huni hvni
          (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient
            (f ⊗ₜ[ℂ] ℓ))) x =
      Induction.eval Q (leviInflatedInducingRepresentation k hV B) (J f) x.1 ⊗ₜ[ℂ]
        Induction.eval Q (leviInflatedInducingRepresentation k hV B.contragredient)
          (reverseInducedDualInverse h k hU hV A B R hR ℓ) x.2 := by
  rw [reverseDualTensorComparison_tmul,
    leviNormalizedProductInductionTensorEquiv_tmul_eval]

/-- Equivariance for the actual G x G action holds on every coefficient vector. -/
theorem reverseDualTensorComparison_action
    (x : G × G) (F : leviProductInducedCoefficientObject h hU A) :
    reverseDualTensorComparison h k hU hV A B J R hR huni hvni
        ((leviProductInducedCoefficientObject h hU A).representation x F) =
      (leviProductInducedCoefficientObject k hV B).representation x
        (reverseDualTensorComparison h k hU hV A B J R hR huni hvni F) :=
  congrArg (fun T => T F)
    ((reverseDualTensorComparison h k hU hV A B J R hR huni hvni).isIntertwining' x)

/-- A bijective forward operator makes this particular tensor bijective. -/
theorem reverseDualTensorComparison_bijective (hJ : Function.Bijective J) :
    Function.Bijective (reverseDualTensorComparison h k hU hV A B J R hR huni hvni) := by
  let E := TensorProduct.congr (J.ofBijective hJ).toLinearEquiv
    (R.ofBijective hR).symm.toLinearEquiv
  have ht : Function.Bijective (reverseDualTensorIntertwiner h k hU hV A B J R hR) :=
    E.bijective
  exact (leviNormalizedProductInductionTensorEquiv k k hV hV hvni hvni B B.contragredient).bijective.comp
    (ht.comp
      (leviNormalizedProductInductionTensorEquiv h h hU hU huni huni A A.contragredient).symm.bijective)

/-- The same scalar cancellation holds after the actual product comparisons. -/
theorem reverseDualTensorComparison_rescale (c : ℂ) (hc : c ≠ 0) :
    reverseDualTensorComparison h k hU hV A B (c • J) (c • R)
        (reverseInducedDual_rescale_bijective h k hU hV A B R hR c hc) huni hvni =
      reverseDualTensorComparison h k hU hV A B J R hR huni hvni := by
  unfold reverseDualTensorComparison
  rw [reverseDualTensorIntertwiner_rescale h k hU hV A B J R hR c hc]

end Langlands.Plancherel
