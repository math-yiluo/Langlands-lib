import Langlands.Algebra.SeparableTensorStatement
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Proof of the finite separable tensor decomposition -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra.SeparableTensor

theorem embeddingEvaluationStatement : EmbeddingEvaluationStatement.{u,v,w} := by
  intro k K Ω _ _ _ _ _ _ _ hsplit
  let F : (K →ₐ[k] Ω) → Module.Dual Ω (Ω ⊗[k] K) :=
    fun σ => LinearMap.liftBaseChangeEquiv Ω σ.toLinearMap
  have hli : LinearIndependent Ω F :=
    (linearIndependent_algHom_toLinearMap k K Ω).map'
      (LinearMap.liftBaseChangeEquiv Ω).toLinearMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.liftBaseChangeEquiv Ω).injective)
  have hcard : Fintype.card (K →ₐ[k] Ω) =
      Module.finrank Ω (Module.Dual Ω (Ω ⊗[k] K)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_baseChange]
    exact AlgHom.card_of_splits k K Ω hsplit
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hinj : Function.Injective (embeddingEvaluation k K Ω).toLinearMap := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    apply (Module.eval_apply_eq_zero_iff Ω x).mp
    apply LinearMap.ext_on_range hspan
    intro σ
    change F σ x = 0
    exact congrFun hx σ
  have hdim : Module.finrank Ω (Ω ⊗[k] K) =
      Module.finrank Ω ((K →ₐ[k] Ω) → Ω) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]
    exact (AlgHom.card_of_splits k K Ω hsplit).symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end Langlands.Algebra.SeparableTensor
