import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Pi

/-! # Evaluation of a scalar extension at algebra homomorphisms -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra.SeparableTensor

variable (k : Type u) (K : Type v) (Ω : Type w)
  [CommSemiring k] [CommSemiring K] [CommSemiring Ω] [Algebra k K] [Algebra k Ω]

/-- The canonical evaluation map, with one coordinate for each `k`-algebra map `K → Ω`. -/
def embeddingEvaluation : Ω ⊗[k] K →ₐ[Ω] ((K →ₐ[k] Ω) → Ω) :=
  AlgHom.pi fun σ => AlgHom.liftEquiv k Ω K Ω σ

@[simp] theorem embeddingEvaluation_apply (x : Ω ⊗[k] K) (σ : K →ₐ[k] Ω) :
    embeddingEvaluation k K Ω x σ = AlgHom.liftEquiv k Ω K Ω σ x :=
  rfl

@[simp] theorem embeddingEvaluation_tmul (c : Ω) (x : K) (σ : K →ₐ[k] Ω) :
    embeddingEvaluation k K Ω (c ⊗ₜ x) σ = c * σ x :=
  rfl

/-- Each coordinate of evaluation is the scalar extension of the corresponding linear map. -/
theorem embeddingEvaluation_linearMap (σ : K →ₐ[k] Ω) :
    (AlgHom.liftEquiv k Ω K Ω σ).toLinearMap =
      LinearMap.liftBaseChangeEquiv Ω σ.toLinearMap :=
  rfl

end Langlands.Algebra.SeparableTensor
