import Langlands.Analysis.Local.CompactQuotientHilbertSchmidtStatement
import Langlands.Analysis.Local.QuotientConvolutionKernelProof
import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof

/-! # Hilbert–Schmidt convolution on a compact left coset space -/

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open Langlands.Analysis Langlands.Analysis.OperatorIdeals

/-- Compactness bounds the norms of the continuous family of evaluation vectors,
so compactly supported convolution is Hilbert–Schmidt. -/
theorem compactQuotientIntegratedHilbertSchmidt :
    CompactQuotientIntegratedHilbertSchmidtStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ _ ν _ hν hcompact
    π hπnorm hπmeas hπapply f hf
  let := hcompact
  let : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨v, hvc, hvpair, _⟩ := quotientConvolutionKernel H hH μH μG ν hν f
  have hcoset (h : H) (x : G) :
      leftQuotientMap H (h.val * x) = leftQuotientMap H x := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simp [mul_inv_rev]
  have hvinv (h : H) (x : G) : v (h.val * x) = v x := by
    apply (innerSL_inj (𝕜 := ℂ)).mp
    ext φ
    rw [innerSL_apply_apply, innerSL_apply_apply, (hvpair _ φ).2, (hvpair x φ).2]
    simp only [mul_assoc, hcoset]
  let vQ := descend H v hvinv
  have hvQc : Continuous vQ := hvc.quotient_lift _
  obtain ⟨C, hC⟩ := (isCompact_range hvQc.norm).bddAbove
  let k (q : LeftQuotient H) := innerSL ℂ (vQ q)
  have hk (q : LeftQuotient H) : ‖k q‖ ≤ max C 0 := by
    rw [show ‖k q‖ = ‖vQ q‖ from innerSL_apply_norm ℂ (vQ q)]
    exact (hC ⟨q, rfl⟩).trans (le_max_left _ _)
  have hq := leftQuotient_isOpenQuotientMap H
  have hact : Continuous (fun p : LeftQuotient H × G => rightTranslate H p.2 p.1) := by
    have hprod := hq.prodMap (IsOpenQuotientMap.id : IsOpenQuotientMap (id : G → G))
    rw [← hprod.continuous_comp_iff]
    exact hq.continuous.comp (continuous_fst.mul continuous_snd)
  have hpoint := integratedTranslationPointwise (LeftQuotient H) ν G μG
    (fun q a => rightTranslate H a q) hact.measurable hν.right_invariant π hπnorm hπmeas
    hπapply f hf
  refine (hilbertSchmidtUniformEvaluation.{uG, uG, uG} (Lp ℂ 2 ν) (LeftQuotient H) ν
    (integratedIsometricAction μG π hπnorm hπmeas f hf) k (max C 0) (le_max_right _ _)
    ?_ (Filter.Eventually.of_forall hk)).1
  intro φ
  filter_upwards [(hpoint φ).2] with q hq'
  refine hq'.trans ?_
  induction q using Quotient.inductionOn with
  | h x => exact (hvpair x φ).2.symm

end Langlands.QuotientIntegration
