import Langlands.Analysis.HilbertSchmidtBasisStatement
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum

noncomputable section

open scoped ENNReal

namespace Langlands.Analysis.OperatorIdeals

universe u v w z t

variable {E : Type u} {F : Type v} {ι : Type w} {κ : Type z} {τ : Type t}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
private theorem basis_hasSum_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using
    (lp.hasSum_norm (p := 2) (by norm_num) (b.repr x))

omit [CompleteSpace E] in
private theorem basis_ennreal_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (basis_hasSum_norm_sq b x).summable, (basis_hasSum_norm_sq b x).tsum_eq]

private theorem basis_ennreal_sum_adjoint (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis τ ℂ F) :
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2) := by
  calc
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (d j) (A (b i))‖ ^ 2) := by
          apply tsum_congr
          intro i
          exact (basis_ennreal_norm_sq d (A (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (d j) (A (b i))‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (A.adjoint (d j))‖ ^ 2) := by
      apply tsum_congr
      intro j
      apply tsum_congr
      intro i
      rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖A.adjoint (d j)‖ ^ 2) := by
      apply tsum_congr
      intro j
      exact basis_ennreal_norm_sq b (A.adjoint (d j))

private theorem basis_ennreal_sum_eq (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    (∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖A (c j)‖ ^ 2) := by
  obtain ⟨s, d, _⟩ := exists_hilbertBasis ℂ F
  exact (basis_ennreal_sum_adjoint A b d).trans (basis_ennreal_sum_adjoint A c d).symm

private theorem basis_summable_transfer (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (h : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    Summable (fun j => ‖A (c j)‖ ^ 2) := by
  have hc : (∑' j, ENNReal.ofReal (‖A (c j)‖ ^ 2)) ≠ ∞ := by
    rw [← basis_ennreal_sum_eq A b c]
    exact h.tsum_ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hc

private theorem basis_independence_complete (A : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) :
    (Summable (fun i => ‖A (b i)‖ ^ 2) ↔ Summable (fun j => ‖A (c j)‖ ^ 2)) ∧
      (Summable (fun i => ‖A (b i)‖ ^ 2) →
        (∑' i, ‖A (b i)‖ ^ 2) = ∑' j, ‖A (c j)‖ ^ 2) := by
  refine ⟨⟨basis_summable_transfer A b c, basis_summable_transfer A c b⟩, ?_⟩
  intro hb
  have hc := basis_summable_transfer A b c hb
  have he : ENNReal.ofReal (∑' i, ‖A (b i)‖ ^ 2) =
      ENNReal.ofReal (∑' j, ‖A (c j)‖ ^ 2) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hb,
      ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hc]
    exact basis_ennreal_sum_eq A b c
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _))] using
    congrArg ENNReal.toReal he

variable (E F ι κ) in
omit [CompleteSpace E] [CompleteSpace F] in
theorem hilbertSchmidtBasisIndependence :
    HilbertSchmidtBasisIndependenceStatement E F ι κ := by
  intro A b c
  have : CompleteSpace E := b.repr.toIsometryEquiv.completeSpace
  let A' : E →L[ℂ] UniformSpace.Completion F := UniformSpace.Completion.toComplL.comp A
  have hA : ∀ x, ‖A' x‖ = ‖A x‖ := fun x => UniformSpace.Completion.norm_coe (A x)
  simpa only [hA] using basis_independence_complete A' b c

end Langlands.Analysis.OperatorIdeals
