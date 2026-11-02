import Langlands.Representation.Unitary.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Complete inner-product models of form-dependent Hilbert completions -/

noncomputable section
set_option autoImplicit false

namespace Langlands.InvariantPositiveForm

universe uG uV uE

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
  (b : InvariantPositiveForm ρ)
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (e : V ≃ₗ[ℂ] E) (he : ∀ v w, inner ℂ (e v) (e w) = b.inner v w)

include he

/-- A form-preserving model identifies the form-normed carrier isometrically. -/
def normedModelEquiv : b.NormedCarrier ≃ₗᵢ[ℂ] E :=
  (b.toNormedCarrier.symm.trans e).isometryOfInner (fun v w => he v w)

@[simp]
theorem normedModelEquiv_toNormedCarrier (v : V) :
    b.normedModelEquiv e he (b.toNormedCarrier v) = e v := rfl

/-- The supplied scalar-product identity gives the norm identity at the dense
embedding, without assigning a topology to the original algebraic carrier. -/
theorem model_norm_eq_toHilbert (v : V) : ‖e v‖ = ‖b.toHilbert v‖ := by
  calc
    ‖e v‖ = ‖b.toNormedCarrier v‖ := (b.normedModelEquiv e he).norm_map _
    _ = ‖b.toHilbert v‖ :=
      (UniformSpace.Completion.norm_coe (b.toNormedCarrier v)).symm

variable [CompleteSpace E]

/-- Extend the actual model to an isometric equivalence with the actual
Hilbert completion. The complete model is supplied; the equivalence is constructed. -/
def completeModelEquiv : b.HilbertCompletion ≃ₗᵢ[ℂ] E :=
  e.extendOfIsometry b.toHilbert (LinearMap.id : E →ₗ[ℂ] E)
    b.denseRange_toHilbert (Function.surjective_id.denseRange)
    (b.model_norm_eq_toHilbert e he)

@[simp]
theorem completeModelEquiv_toHilbert (v : V) :
    b.completeModelEquiv e he (b.toHilbert v) = e v :=
  LinearEquiv.extendOfIsometry_eq e b.toHilbert (LinearMap.id : E →ₗ[ℂ] E)
    b.denseRange_toHilbert Function.surjective_id.denseRange
    (b.model_norm_eq_toHilbert e he) v

@[simp]
theorem completeModelEquiv_symm_apply (y : E) :
    (b.completeModelEquiv e he).symm y = b.toHilbert (e.symm y) :=
  LinearEquiv.extendOfIsometry_symm_eq e b.toHilbert (LinearMap.id : E →ₗ[ℂ] E)
    b.denseRange_toHilbert Function.surjective_id.denseRange
    (b.model_norm_eq_toHilbert e he) y

/-- When the algebraic carrier already has a complete form-preserving model,
every vector of its completion is an embedded original vector. -/
theorem toHilbert_surjective_of_completeModel : Function.Surjective b.toHilbert := by
  intro x
  refine ⟨e.symm (b.completeModelEquiv e he x), ?_⟩
  apply (b.completeModelEquiv e he).injective
  rw [completeModelEquiv_toHilbert, LinearEquiv.apply_symm_apply]

/-- Density makes the prescribed continuous linear extension unique. -/
theorem completeModelEquiv_unique (M : b.HilbertCompletion →L[ℂ] E)
    (hM : ∀ v, M (b.toHilbert v) = e v) :
    M = (b.completeModelEquiv e he).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq M.continuous (b.completeModelEquiv e he).continuous
  · intro v
    exact (hM v).trans (b.completeModelEquiv_toHilbert e he v).symm

/-- Any further algebraic operator identity extends to the whole model when
the operators have the specified continuous extensions. -/
theorem completeModelEquiv_covariant
    (a : Module.End ℂ V)
    (A : b.HilbertCompletion →L[ℂ] b.HilbertCompletion) (D : E →L[ℂ] E)
    (hA : ∀ v, A (b.toHilbert v) = b.toHilbert (a v))
    (heD : ∀ v, e (a v) = D (e v)) (x : b.HilbertCompletion) :
    b.completeModelEquiv e he (A x) = D (b.completeModelEquiv e he x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq ((b.completeModelEquiv e he).continuous.comp A.continuous)
      (D.continuous.comp (b.completeModelEquiv e he).continuous)
  · intro v
    rw [hA, completeModelEquiv_toHilbert, completeModelEquiv_toHilbert, heD]

/-- The completed group operator is conjugate to any matching continuous
operator on the complete model. -/
theorem completeModelEquiv_completedOperator (g : G) (D : E →L[ℂ] E)
    (heD : ∀ v, e (ρ g v) = D (e v)) (x : b.HilbertCompletion) :
    b.completeModelEquiv e he (b.completedOperator g x) =
      D (b.completeModelEquiv e he x) :=
  b.completeModelEquiv_covariant e he (ρ g)
    (b.completedOperator g).toLinearIsometry.toContinuousLinearMap D
    (b.completedOperator_toHilbert g) heD x

end Langlands.InvariantPositiveForm
