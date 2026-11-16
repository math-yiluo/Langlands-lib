import Langlands.Representation.Plancherel.LeviNormalizedProductCoefficients
import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Representation.Aubert.General.ContragredientTransport

/-! # Actual left translation on source-normalized coefficient fibers -/

noncomputable section

set_option maxRecDepth 4096

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Plancherel.CoefficientConjugation

open Aubert.General

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U P' M' U' : Subgroup G}

/-- Transport an actual Levi-normalized induction through an inducing
equivalence, retaining independent carrier universes. -/
def leviInductionCongr (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (e : A.representation.Equiv B.representation) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj B).representation :=
  ((normalizedInductionLeviEquiv h hU hδ A).symm.trans
    (normalizedInductionEquivOfEquiv h hU e)).trans
      (normalizedInductionLeviEquiv h hU hδ B)

@[simp]
theorem leviInductionCongr_eval (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
    (e : A.representation.Equiv B.representation)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (x : G) :
    Induction.eval P (leviInflatedInducingRepresentation h hU B)
        (leviInductionCongr h hU hδ e f) x =
      e (Induction.eval P (leviInflatedInducingRepresentation h hU A) f x) := rfl

variable (h : IsSemidirectDecomposition P M U)
  (h' : IsSemidirectDecomposition P' M' U') (g : G)
  (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
  (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
  (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
  (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
  (hδ : IsUnimodularModulus U hU) (hδ' : IsUnimodularModulus U' hU')
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- Actual left translation, transported through the value-preserving
normalization comparisons. -/
def leviLeftTranslation :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
        ((conjugationFunctor g hMM').obj A)).representation :=
  ((normalizedInductionLeviEquiv h hU hδ A).symm.trans
    (SmoothRep.equivOfIso
      (inductionConjugationIsoApp h h' g hPP' hMM' hUU' hU hU' A))).trans
        (normalizedInductionLeviEquiv h' hU' hδ'
          ((conjugationFunctor g hMM').obj A))

@[simp]
theorem leviLeftTranslation_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (x : G) :
    Induction.eval P'
        (leviInflatedInducingRepresentation h' hU' ((conjugationFunctor g hMM').obj A))
        (leviLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A f) x =
      Induction.eval P (leviInflatedInducingRepresentation h hU A) f (g⁻¹ * x) := rfl

omit h h' hPP' hUU' hU hU' hδ hδ' in
/-- The canonical same-functional identification of the conjugate smooth
dual with the smooth dual of the conjugate. -/
def conjugateDualEquiv :
    ((conjugationFunctor g hMM').obj A.contragredient).representation.Equiv
      ((conjugationFunctor g hMM').obj A).contragredient.representation :=
  SmoothRep.equivOfIso
    (contragredientPullbackIso (conjugationEquiv g hMM') A).symm

omit h h' hPP' hUU' hU hU' hδ hδ' [LocallyCompactSpace G] in
@[simp]
theorem conjugateDualEquiv_apply
    (ℓ : (conjugationFunctor g hMM').obj A.contragredient) (v : A) :
    (conjugateDualEquiv g hMM' A ℓ).val v = ℓ.val v := rfl

/-- The dual tensor factor uses left translation followed by the actual
smooth-dual pullback identification. -/
def leviDualLeftTranslation :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj
      A.contragredient).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h' hU').obj
        ((conjugationFunctor g hMM').obj A).contragredient).representation :=
  (leviLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A.contragredient).trans
    (leviInductionCongr h' hU' hδ' (conjugateDualEquiv g hMM' A))

@[simp]
theorem leviDualLeftTranslation_eval
    (j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient)
    (x : G) :
    Induction.eval P' (leviInflatedInducingRepresentation h' hU'
        ((conjugationFunctor g hMM').obj A).contragredient)
        (leviDualLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A j) x =
      conjugateDualEquiv g hMM' A
        (Induction.eval P (leviInflatedInducingRepresentation h hU A.contragredient)
          j (g⁻¹ * x)) := rfl

@[simp]
theorem leviDualLeftTranslation_eval_apply
    (j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient)
    (x : G) (v : A) :
    (Induction.eval P' (leviInflatedInducingRepresentation h' hU'
        ((conjugationFunctor g hMM').obj A).contragredient)
        (leviDualLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A j) x).val v =
      (Induction.eval P (leviInflatedInducingRepresentation h hU A.contragredient)
        j (g⁻¹ * x)).val v := rfl

variable [SecondCountableTopology G]
  [CompactSpace (Induction.LeftQuotient P)]
  [CompactSpace (Induction.LeftQuotient P')]

/-- Tensoring the actual two left translations gives the comparison between
the original source-normalized product coefficient fibers. -/
def leviCoefficientLeftTranslation :
    (leviProductInducedCoefficientObject h hU A).representation.Equiv
      (leviProductInducedCoefficientObject h' hU'
        ((conjugationFunctor g hMM').obj A)).representation :=
  ((leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ
      A A.contragredient).symm.trans
    (FiniteTensorFiltration.tprodCongr
      (Induction.BinaryTensor.pullEquiv
        (leviLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A)
        (MonoidHom.fst G G))
      (Induction.BinaryTensor.pullEquiv
        (leviDualLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A)
        (MonoidHom.snd G G)))).trans
    (leviNormalizedProductInductionTensorEquiv h' h' hU' hU' hδ' hδ'
      ((conjugationFunctor g hMM').obj A)
      ((conjugationFunctor g hMM').obj A).contragredient)

/-- Pure tensors follow the two actual inducing translations. -/
@[simp]
theorem leviCoefficientLeftTranslation_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient) :
    leviCoefficientLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A
        (leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ
          A A.contragredient (f ⊗ₜ[ℂ] j)) =
      leviNormalizedProductInductionTensorEquiv h' h' hU' hU' hδ' hδ'
        ((conjugationFunctor g hMM').obj A)
        ((conjugationFunctor g hMM').obj A).contragredient
        (leviLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A f ⊗ₜ[ℂ]
          leviDualLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A j) := by
  change
    leviNormalizedProductInductionTensorEquiv h' h' hU' hU' hδ' hδ'
      ((conjugationFunctor g hMM').obj A)
      ((conjugationFunctor g hMM').obj A).contragredient
      (TensorProduct.congr
        (leviLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A).toLinearEquiv
        (leviDualLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A).toLinearEquiv
        ((leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ
          A A.contragredient).symm
          (leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ
            A A.contragredient (f ⊗ₜ[ℂ] j)))) = _
  rw [Representation.Equiv.symm_apply_apply]
  rfl

/-- Evaluation after the product-induction comparisons retains the original
function values and the actual dual identification. -/
theorem leviCoefficientLeftTranslation_tmul_eval
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (j : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A.contragredient)
    (x : G × G) :
    Induction.eval (P'.prod P')
        (leviInflatedInducingRepresentation (h'.prod h') (hU'.prod hU')
          (productLeviObject ((conjugationFunctor g hMM').obj A)
            ((conjugationFunctor g hMM').obj A).contragredient))
        (leviCoefficientLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A
          (leviNormalizedProductInductionTensorEquiv h h hU hU hδ hδ
            A A.contragredient (f ⊗ₜ[ℂ] j))) x =
      Induction.eval P (leviInflatedInducingRepresentation h hU A) f (g⁻¹ * x.1) ⊗ₜ[ℂ]
        conjugateDualEquiv g hMM' A
          (Induction.eval P (leviInflatedInducingRepresentation h hU A.contragredient)
            j (g⁻¹ * x.2)) := by
  rw [leviCoefficientLeftTranslation_tmul,
    leviNormalizedProductInductionTensorEquiv_tmul_eval,
    leviLeftTranslation_eval, leviDualLeftTranslation_eval]
  rfl

/-- The constructed coefficient comparison intertwines the original
external product action on every vector. -/
theorem leviCoefficientLeftTranslation_action (z : G × G)
    (F : leviProductInducedCoefficientObject h hU A) :
    leviCoefficientLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A
        ((leviProductInducedCoefficientObject h hU A).representation z F) =
      (leviProductInducedCoefficientObject h' hU'
        ((conjugationFunctor g hMM').obj A)).representation z
        (leviCoefficientLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A F) :=
  congrArg (fun T : leviProductInducedCoefficientObject h hU A →ₗ[ℂ]
    leviProductInducedCoefficientObject h' hU'
      ((conjugationFunctor g hMM').obj A) => T F)
    ((leviCoefficientLeftTranslation h h' g hPP' hMM' hUU' hU hU' hδ hδ' A).isIntertwining' z)

end Langlands.Plancherel.CoefficientConjugation
