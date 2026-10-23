import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
universe u
open NumberField Module
open scoped TensorProduct

namespace Langlands.Global.TotallyReal

variable (E : Type u) [Field E] [NumberField E] [IsTotallyReal E]

/-- Real and complex embeddings coincide for a totally real field. -/
def realComplexEmbeddings : (E →+* ℝ) ≃ (E →+* ℂ) where
  toFun τ := Complex.ofRealHom.comp τ
  invFun φ := (IsTotallyReal.complexEmbedding_isReal φ).embedding
  left_inv τ := by ext x; rfl
  right_inv φ := by
    ext x
    exact ComplexEmbedding.IsReal.coe_embedding_apply _ x

/-- The actual product of the real embeddings. -/
def evaluation : E →ₐ[ℚ] ((E →+* ℝ) → ℝ) :=
  (RingHom.pi fun τ => τ).toRatAlgHom

omit [IsTotallyReal E] in
@[simp] theorem evaluation_apply (x : E) (τ : E →+* ℝ) : evaluation E x τ = τ x := rfl

/-- Scalar extension of evaluation, with its actual tensor formula. -/
def tensorEvaluation : ℝ ⊗[ℚ] E →ₐ[ℝ] ((E →+* ℝ) → ℝ) :=
  AlgHom.liftEquiv ℚ ℝ E _ (evaluation E)

omit [IsTotallyReal E] in
@[simp] theorem tensorEvaluation_tmul (r : ℝ) (x : E) (τ : E →+* ℝ) :
    tensorEvaluation E (r ⊗ₜ[ℚ] x) τ = r * τ x := rfl

/-- Real evaluation vectors become the usual complex evaluation vectors. -/
private def complexify : ((E →+* ℝ) → ℝ) →ₗ[ℝ] ((E →+* ℂ) → ℂ) where
  toFun f φ := (f ((realComplexEmbeddings E).symm φ) : ℂ)
  map_add' f g := by ext φ; simp
  map_smul' r f := by ext φ; simp

private theorem evaluation_integralBasis_independent :
    LinearIndependent ℝ (fun i => evaluation E (integralBasis E i)) := by
  apply LinearIndependent.of_comp (complexify E)
  have h := (canonicalEmbedding.latticeBasis E).linearIndependent.restrict_scalars' ℝ
  convert h using 1
  funext i φ
  change (((IsTotallyReal.complexEmbedding_isReal φ).embedding
    (integralBasis E i)) : ℂ) = canonicalEmbedding.latticeBasis E i φ
  rw [canonicalEmbedding.latticeBasis_apply]
  exact ComplexEmbedding.IsReal.coe_embedding_apply _ _

/-- The integral basis evaluated at all real embeddings is a real basis. -/
def evaluationBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ ((E →+* ℝ) → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => evaluation E (integralBasis E i))
    (evaluation_integralBasis_independent E) (by
      rw [Module.finrank_fintype_fun_eq_card,
        Fintype.card_congr (realComplexEmbeddings E), Embeddings.card E ℂ]
      exact (Module.finrank_eq_card_basis (integralBasis E)).symm)

@[simp] theorem evaluationBasis_apply (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    evaluationBasis E i = evaluation E (integralBasis E i) := by
  simp [evaluationBasis]

/-- Evaluation is bijective, proved by comparison with two actual bases. -/
theorem tensorEvaluation_bijective : Function.Bijective (tensorEvaluation E) := by
  let e := ((integralBasis E).baseChange ℝ).equiv (evaluationBasis E) (Equiv.refl _)
  have he : (tensorEvaluation E).toLinearMap = e.toLinearMap := by
    apply ((integralBasis E).baseChange ℝ).ext
    intro i
    change tensorEvaluation E (((integralBasis E).baseChange ℝ) i) =
      ((integralBasis E).baseChange ℝ).equiv (evaluationBasis E) (Equiv.refl _) _
    rw [Basis.equiv_apply, Basis.baseChange_apply, evaluationBasis_apply]
    ext τ
    exact one_mul _
  change Function.Bijective (tensorEvaluation E).toLinearMap
  rw [he]
  exact e.bijective

/-- The real scalar extension of a totally real number field splits by its real embeddings. -/
def tensorEquiv : ℝ ⊗[ℚ] E ≃ₐ[ℝ] ((E →+* ℝ) → ℝ) :=
  AlgEquiv.ofBijective (tensorEvaluation E) (tensorEvaluation_bijective E)

@[simp] theorem tensorEquiv_tmul (r : ℝ) (x : E) (τ : E →+* ℝ) :
    tensorEquiv E (r ⊗ₜ[ℚ] x) τ = r * τ x := rfl

end Langlands.Global.TotallyReal
