import Langlands.Representation.Plancherel.ActualConjugateLeviTensor

noncomputable section

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types true

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.TranslatedStandardTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualConjugateLeviTwist ActualConjugateLeviTensor

section TranslationLaw

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U P' M' U' : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition P' M' U')
  (g : H) (hP : ∀ x : H, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
  (hU' : ∀ x : H, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (U' : Set H))
  (hδ : IsUnimodularModulus U hc) (hδ' : IsUnimodularModulus U' hc')
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ M')
  (e : ((conjugationFunctor g hM).obj A).representation.Equiv B.representation)
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient P')]

private theorem coefficientCongr_after_translation_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient) :
    coefficientCongr k hc' hδ' e
      (CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A
        (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
          (f ⊗ₜ[ℂ] ℓ))) =
      leviNormalizedProductInductionTensorEquiv k k hc' hc' hδ' hδ' B B.contragredient
        (CoefficientConjugation.leviInductionCongr k hc' hδ' e
          (CoefficientConjugation.leviLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A f) ⊗ₜ[ℂ]
          CoefficientConjugation.leviInductionCongr k hc' hδ'
            (A := ((conjugationFunctor g hM).obj A).contragredient)
            (B := B.contragredient) (smoothContragredientEquiv e.symm)
            (CoefficientConjugation.leviDualLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A ℓ)) := by
  rw [CoefficientConjugation.leviCoefficientLeftTranslation_tmul, coefficientCongr_tmul]

def vectorFactor :=
  (CoefficientConjugation.leviLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A).trans
    (CoefficientConjugation.leviInductionCongr k hc' hδ' (A := (conjugationFunctor g hM).obj A)
      (B := B) e)

def dualFactor :=
  (CoefficientConjugation.leviDualLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A).trans
    (CoefficientConjugation.leviInductionCongr k hc' hδ'
      (A := ((conjugationFunctor g hM).obj A).contragredient)
      (B := B.contragredient) (smoothContragredientEquiv e.symm))

variable {P'' U'' : Subgroup H}
  (t : IsSemidirectDecomposition P'' M' U'')
  (hct : IsClosed (U'' : Set H)) (hδt : IsUnimodularModulus U'' hct)
  (J : ((DynamicNormalization.leviTwistedInductionFunctor k hc').obj B).representation.IntertwiningMap
    ((DynamicNormalization.leviTwistedInductionFunctor t hct).obj B).representation)
  (R : ((DynamicNormalization.leviTwistedInductionFunctor t hct).obj B.contragredient).representation.IntertwiningMap
    ((DynamicNormalization.leviTwistedInductionFunctor k hc').obj B.contragredient).representation)
  (hR : Function.Bijective R) [CompactSpace (Induction.LeftQuotient P'')]

set_option hygiene false in
local notation "EV" => vectorFactor h k g hP hM hU' hc hc' hδ hδ' A B e
set_option hygiene false in
local notation "ED" => dualFactor h k g hP hM hU' hc hc' hδ hδ' A B e

/-- Expanded pure-tensor formula for the constructed translation followed by
the specified forward and inverse reverse-dual standard factors. -/
def ExpandedTensorFormula : Prop :=
  ∀ (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient),
    reverseDualTensorComparison k t hc' hct B B J R hR hδ' hδt
      (coefficientCongr k hc' hδ' e
        (CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A
          (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
            (f ⊗ₜ[ℂ] ℓ)))) =
      leviNormalizedProductInductionTensorEquiv t t hct hct hδt hδt B B.contragredient
        (J (EV f) ⊗ₜ[ℂ] reverseInducedDualInverse k t hc' hct B B R hR (ED ℓ))

/-- The expanded formula is elementary algebra of the actual constructed maps. -/
theorem expandedTensorFormula :
    ExpandedTensorFormula h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR := by
  intro f ℓ
  exact (congrArg (reverseDualTensorComparison k t hc' hct B B J R hR hδ' hδt)
    (coefficientCongr_after_translation_tmul h k g hP hM hU' hc hc' hδ hδ' A B e f ℓ)).trans
      (reverseDualTensorComparison_tmul k t hc' hct B B J R hR hδ' hδt (EV f) (ED ℓ))

/-- Expanded evaluation formula on the exact product-induced coefficient
model, retaining the order of the two coordinates. -/
def ExpandedEvaluationFormula : Prop :=
  ∀ (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient)
    (x : H × H),
    Induction.eval (P''.prod P'')
      (leviInflatedInducingRepresentation (t.prod t) (hct.prod hct)
        (productLeviObject B B.contragredient))
      (reverseDualTensorComparison k t hc' hct B B J R hR hδ' hδt
        (coefficientCongr k hc' hδ' e
          (CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A
            (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
              (f ⊗ₜ[ℂ] ℓ))))) x =
      Induction.eval P'' (leviInflatedInducingRepresentation t hct B) (J (EV f)) x.1 ⊗ₜ[ℂ]
      Induction.eval P'' (leviInflatedInducingRepresentation t hct B.contragredient)
        (reverseInducedDualInverse k t hc' hct B B R hR (ED ℓ)) x.2

/-- Evaluation follows from the proved pure formula and the existing
positive-Levi tensor evaluation law. -/
theorem expandedEvaluationFormula :
    ExpandedEvaluationFormula h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR := by
  intro f ℓ x
  exact (congrArg
    (fun v => Induction.eval (P''.prod P'')
      (leviInflatedInducingRepresentation (t.prod t) (hct.prod hct)
        (productLeviObject B B.contragredient)) v x)
    (expandedTensorFormula h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR f ℓ)).trans
      (leviNormalizedProductInductionTensorEquiv_tmul_eval t t hct hct hδt hδt
        B B.contragredient (J (EV f))
        (reverseInducedDualInverse k t hc' hct B B R hR (ED ℓ)) x)

/-- The literal coefficient composite of actual left translation, pointwise
inducing transport, and the specified forward/inverse-reverse-dual tensor. -/
def comparison :
    (leviProductInducedCoefficientObject h hc A).representation.IntertwiningMap
      (leviProductInducedCoefficientObject t hct B).representation :=
  (reverseDualTensorComparison k t hc' hct B B J R hR hδ' hδt).comp
    ((CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A).trans
      (coefficientCongr k hc' hδ' e)).toIntertwiningMap

/-- The full forward/translation and inverse-reverse/dual-translation formula
on pure tensors for the literal constructed coefficient composite. -/
theorem comparison_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient) :
    comparison h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR
      (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
        (f ⊗ₜ[ℂ] ℓ)) =
      leviNormalizedProductInductionTensorEquiv t t hct hct hδt hδt B B.contragredient
        (J (EV f) ⊗ₜ[ℂ] reverseInducedDualInverse k t hc' hct B B R hR (ED ℓ)) :=
  expandedTensorFormula h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR f ℓ

/-- Product-induction evaluation of that same literal composite. -/
theorem comparison_tmul_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient)
    (x : H × H) :
    Induction.eval (P''.prod P'')
      (leviInflatedInducingRepresentation (t.prod t) (hct.prod hct)
        (productLeviObject B B.contragredient))
      (comparison h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR
        (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
          (f ⊗ₜ[ℂ] ℓ))) x =
      Induction.eval P'' (leviInflatedInducingRepresentation t hct B) (J (EV f)) x.1 ⊗ₜ[ℂ]
      Induction.eval P'' (leviInflatedInducingRepresentation t hct B.contragredient)
        (reverseInducedDualInverse k t hc' hct B B R hR (ED ℓ)) x.2 :=
  expandedEvaluationFormula h k g hP hM hU' hc hc' hδ hδ' A B e t hct hδt J R hR f ℓ x

end TranslationLaw

end Langlands.Plancherel.TranslatedStandardTensor
