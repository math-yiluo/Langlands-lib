import Langlands.Analysis.HilbertSchmidtProductTraceClassStatement
import Langlands.Analysis.HilbertSchmidtProductTraceProof
import Langlands.Analysis.HilbertSchmidtIdealProof
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem product_modulus_adjoint (A : E →L[ℂ] E) :
    (leftModulus A).adjoint = leftModulus A :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (CFC.sqrt_nonneg (A * star A))).isSelfAdjoint

private theorem product_modulus_adjoint_norm (A : E →L[ℂ] E) (x : E) :
    ‖A.adjoint x‖ = ‖leftModulus A x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right, product_modulus_adjoint]
  change (inner ℂ x ((A * star A) x)).re =
    (inner ℂ x ((leftModulus A * leftModulus A) x)).re
  rw [show leftModulus A * leftModulus A = A * star A from
    CFC.sqrt_mul_sqrt_self (A * star A) (mul_star_self_nonneg A)]

private theorem product_modulus_factorization (A : E →L[ℂ] E) :
    ∃ U : E →L[ℂ] E, leftModulus A = A.comp U := by
  let g := A.adjoint
  let R := g.toLinearMap.range
  let S := R.topologicalClosure
  let e : E →L[ℂ] S := g.codRestrict S
    (fun x => R.le_topologicalClosure (LinearMap.mem_range_self g.toLinearMap x))
  have he : DenseRange e := by
    change DenseRange (Set.inclusion R.le_topologicalClosure ∘ Set.rangeFactorization g)
    exact ((denseRange_inclusion_iff R.le_topologicalClosure).2 (by rfl)).comp
      Set.rangeFactorization_surjective.denseRange
      (continuous_inclusion R.le_topologicalClosure)
  have h : ∀ x, ‖leftModulus A x‖ ≤ 1 * ‖e x‖ := by
    intro x
    change ‖leftModulus A x‖ ≤ 1 * ‖A.adjoint x‖
    rw [product_modulus_adjoint_norm, one_mul]
  let V : S →L[ℂ] E := (leftModulus A).toLinearMap.extendOfNorm e.toLinearMap
  let T : E →L[ℂ] E := V.comp S.orthogonalProjectionOnto
  have hfac : leftModulus A = T.comp A.adjoint := by
    ext x
    change leftModulus A x = V (S.orthogonalProjectionOnto (A.adjoint x))
    have hproj : S.orthogonalProjectionOnto (A.adjoint x) = e x :=
      S.orthogonalProjectionOnto_mem_subspace_eq_self (e x)
    rw [hproj]
    exact (LinearMap.extendOfNorm_eq he ⟨1, h⟩ x).symm
  refine ⟨T.adjoint, ?_⟩
  simpa only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, product_modulus_adjoint] using
    congrArg ContinuousLinearMap.adjoint hfac

theorem hilbertSchmidtProductTraceClass :
    HilbertSchmidtProductTraceClassStatement.{u, v} := by
  intro E F _ _ _ _ _ _ B C hB hC
  obtain ⟨U, hU⟩ := product_modulus_factorization (C.comp B)
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ E
  obtain ⟨t, d, _⟩ := exists_hilbertBasis ℂ F
  have hn := (hilbertSchmidtProductTrace E F s t (B.comp U) C b d
    (isHilbertSchmidt_precomp B U hB) hC).1
  have hs := (Complex.hasSum_re hn.of_norm.hasSum).summable
  refine ⟨s, b, ?_⟩
  simpa only [hU, ContinuousLinearMap.comp_apply] using hs

end Langlands.Analysis.OperatorIdeals
