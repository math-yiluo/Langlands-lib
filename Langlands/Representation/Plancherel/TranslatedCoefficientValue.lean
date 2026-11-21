import Langlands.Representation.Plancherel.ActualConjugateLeviTensor
import Langlands.Representation.Plancherel.ProductCompactPicture
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof

/-! # Evaluation of the actual translated coefficient section -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 280000

universe u uV uW

open CategoryTheory
open scoped NNReal TensorProduct

namespace Langlands.Plancherel.TranslatedCoefficientValue

open Aubert.General Induction
open ActualConjugateLeviTensor

section ProductEvaluation

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U Q N W : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition Q N W)
  (g : H) (hP : ∀ x : H, x ∈ Q ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (hW : ∀ x : H, x ∈ W ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (W : Set H))
  (hu : IsUnimodularModulus U hc) (hu' : IsUnimodularModulus W hc')
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ N)
  (e : ((conjugationFunctor g hM).obj A).representation.Equiv B.representation)

set_option quotPrecheck false in
local notation "lA" => (conjugationFunctor g hM).obj A

omit [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- Conjugation of a product coefficient value uses the original vector and
identifies the smooth dual by the same linear functional. -/
def conjugateValue : CoefficientTensor A ≃ₗ[ℂ] CoefficientTensor lA :=
  TensorProduct.congr (LinearEquiv.refl ℂ A)
    (CoefficientConjugation.conjugateDualEquiv g hM A).toLinearEquiv

variable [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

set_option hygiene false in
local notation "L" => CoefficientConjugation.leviCoefficientLeftTranslation
  h k g hP hM hW hc hc' hu hu' A
set_option quotPrecheck false in
local notation "ρA" => leviInflatedInducingRepresentation (h.prod h) (hc.prod hc)
  (productLeviObject A A.contragredient)
set_option quotPrecheck false in
local notation "ρB" => leviInflatedInducingRepresentation (k.prod k) (hc'.prod hc')
  (productLeviObject B B.contragredient)

/-- Simultaneous left translation followed by the inducing equivalence
acts pointwise on the whole product section. -/
theorem translatedProduct_eval (f : leviProductInducedCoefficientObject h hc A)
    (x : H × H) :
    Induction.eval (Q.prod Q) ρB (coefficientCongr k hc' hu' e (L f)) x =
      productCoefficientLeviEquiv e (conjugateValue g hM A
        (Induction.eval (P.prod P) ρA f ((g, g)⁻¹ * x))) := by
  let T := leviNormalizedProductInductionTensorEquiv h h hc hc hu hu A A.contragredient
  obtain ⟨v, rfl⟩ := T.surjective f
  let evA := FiniteProductTensorBijective.evalLinear (P.prod P) ρA ((g, g)⁻¹ * x)
  let evB := FiniteProductTensorBijective.evalLinear (Q.prod Q) ρB x
  have heq :
      (evB.comp ((coefficientCongr k hc' hu' e).toLinearMap.comp (L).toLinearMap)).comp
          T.toLinearMap =
        ((productCoefficientLeviEquiv e).toLinearMap.comp
          ((conjugateValue g hM A).toLinearMap.comp evA)).comp T.toLinearMap := by
    apply TensorProduct.ext'
    intro a ℓ
    change Induction.eval (Q.prod Q) ρB
        (coefficientCongr k hc' hu' e (L (T (a ⊗ₜ[ℂ] ℓ)))) x =
      productCoefficientLeviEquiv e (conjugateValue g hM A
        (Induction.eval (P.prod P) ρA (T (a ⊗ₜ[ℂ] ℓ)) ((g, g)⁻¹ * x)))
    rw [coefficientCongr_eval]
    apply congrArg (productCoefficientLeviEquiv e)
    exact (CoefficientConjugation.leviCoefficientLeftTranslation_tmul_eval
      h k g hP hM hW hc hc' hu hu' A a ℓ x).trans
      ((congrArg (conjugateValue g hM A)
        (leviNormalizedProductInductionTensorEquiv_tmul_eval h h hc hc hu hu
          A A.contragredient a ℓ ((g, g)⁻¹ * x))).trans rfl).symm
  exact DFunLike.congr_fun heq v

end ProductEvaluation

section UntwistedValue

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M N : Subgroup H} {I J : Type*} (ν : I → (M →* ℝ≥0ˣ)) (ν' : J → (N →* ℝ≥0ˣ))
  (g : H) (hM : ∀ x : H, x ∈ N ↔ g⁻¹ * x * g ∈ M)
  (A : SmoothRep.{0, u, uV} ℂ M)
  (z : unramifiedCharacters ν) (w : unramifiedCharacters ν')

set_option quotPrecheck false in
local notation "Ag" => (conjugationFunctor g hM).obj A
set_option quotPrecheck false in
local notation "Az" => A.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν z)
set_option quotPrecheck false in
local notation "Agw" => (Ag).twist w.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν' w)

/-- If the inducing equivalence on the conjugate twist has identity vector
map, removal of the twists leaves just the fixed coefficient-value conjugation. -/
theorem untwist_conjugateValue
    (e : ((conjugationFunctor g hM).obj Az).representation.Equiv (Agw).representation)
    (he : ∀ v : A, e v = v) (v : CoefficientTensor Az) :
    productCompactTwistTensorEquiv ν' w Ag
        (productCoefficientLeviEquiv e (conjugateValue g hM Az v)) =
      conjugateValue g hM A (productCompactTwistTensorEquiv ν z A v) := by
  have hEq : (productCompactTwistTensorEquiv ν' w Ag).toLinearMap.comp
      ((productCoefficientLeviEquiv e).toLinearMap.comp (conjugateValue g hM Az).toLinearMap) =
      (conjugateValue g hM A).toLinearMap.comp (productCompactTwistTensorEquiv ν z A).toLinearMap := by
    apply TensorProduct.ext'
    intro a ℓ
    have hs (b : A) : e.symm b = b := by
      apply e.injective
      exact (e.apply_symm_apply b).trans (he b).symm
    change e a ⊗ₜ[ℂ] _ = a ⊗ₜ[ℂ] _
    rw [he a]
    congr 1
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    change ℓ.val (e.symm b) = ℓ.val b
    exact congrArg ℓ.val (hs b)
  exact DFunLike.congr_fun hEq v

end UntwistedValue

end Langlands.Plancherel.TranslatedCoefficientValue
