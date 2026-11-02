import Langlands.Analysis.LeftModulusFactorizationStatement
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

private theorem norm_controlled_factorization
    {𝕜 : Type*} [RCLike 𝕜]
    {D : Type u} {H : Type v} {B : Type w}
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]
    (f : D →L[𝕜] B) (g : D →L[𝕜] H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    ∃ T : H →L[𝕜] B, ‖T‖ ≤ C ∧ f = T.comp g := by
  let R := g.toLinearMap.range
  let S := R.topologicalClosure
  let e : D →L[𝕜] S := g.codRestrict S
    (fun x => R.le_topologicalClosure (LinearMap.mem_range_self g.toLinearMap x))
  have he : DenseRange e := by
    change DenseRange (Set.inclusion R.le_topologicalClosure ∘ Set.rangeFactorization g)
    exact ((denseRange_inclusion_iff R.le_topologicalClosure).2 (by rfl)).comp
      Set.rangeFactorization_surjective.denseRange
      (continuous_inclusion R.le_topologicalClosure)
  let V : S →L[𝕜] B := f.toLinearMap.extendOfNorm e.toLinearMap
  have hV : ∀ x : S, ‖V x‖ ≤ C * ‖x‖ :=
    LinearMap.norm_extendOfNorm_apply_le he C h
  let T : H →L[𝕜] B := V.comp S.orthogonalProjectionOnto
  refine ⟨T, T.opNorm_le_bound hC (fun x => ?_), ?_⟩
  · exact (hV _).trans
      (mul_le_mul_of_nonneg_left (S.norm_orthogonalProjectionOnto_apply_le x) hC)
  · ext x
    change f x = V (S.orthogonalProjectionOnto (g x))
    have hproj : S.orthogonalProjectionOnto (g x) = e x :=
      S.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
    rw [hproj]
    exact (LinearMap.extendOfNorm_eq he ⟨C, h⟩ x).symm

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem modulus_adjoint (A : E →L[ℂ] E) :
    (leftModulus A).adjoint = leftModulus A :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (CFC.sqrt_nonneg (A * star A))).isSelfAdjoint

private theorem modulus_adjoint_norm (A : E →L[ℂ] E) (x : E) :
    ‖A.adjoint x‖ = ‖leftModulus A x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, modulus_adjoint]
  change (inner ℂ x ((A * star A) x)).re =
    (inner ℂ x ((leftModulus A * leftModulus A) x)).re
  rw [show leftModulus A * leftModulus A = A * star A from
    CFC.sqrt_mul_sqrt_self (A * star A) (mul_star_self_nonneg A)]

theorem leftModulusFactorization : LeftModulusFactorizationStatement.{u} := by
  intro E _ _ _ A
  obtain ⟨V, hV, hfac⟩ := norm_controlled_factorization A.adjoint
    (leftModulus A) 1 zero_le_one (fun x => by simp [modulus_adjoint_norm A x])
  refine ⟨V.adjoint, ?_, ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using hV
  · simpa only [ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_comp, modulus_adjoint] using
      congrArg ContinuousLinearMap.adjoint hfac

end Langlands.Analysis.OperatorIdeals
