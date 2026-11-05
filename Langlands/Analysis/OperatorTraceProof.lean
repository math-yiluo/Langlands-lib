import Langlands.Analysis.OperatorTraceStatement
import Langlands.Analysis.TraceBasisProof
import Langlands.Analysis.TraceClassIdealProof

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem operatorTraceBasis : OperatorTraceBasisStatement.{u, w} := by
  intro E _ _ _ A ι b hA
  let c := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  have h := traceBasisIndependence E A _ ι c b hA
  exact ⟨h.2.1, h.2.2⟩

theorem operatorTrace_zero : operatorTrace (0 : E →L[ℂ] E) = 0 := by
  simp [operatorTrace, traceIn]

theorem operatorTrace_add (A D : E →L[ℂ] E)
    (hA : IsTraceClass A) (hD : IsTraceClass D) :
    operatorTrace (A + D) = operatorTrace A + operatorTrace D := by
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  have hA' := (operatorTraceBasis E A _ b hA).1.of_norm
  have hD' := (operatorTraceBasis E D _ b hD).1.of_norm
  change (∑' i, inner ℂ (b i) ((A + D) (b i))) =
    (∑' i, inner ℂ (b i) (A (b i))) + ∑' i, inner ℂ (b i) (D (b i))
  simp only [add_apply, inner_add_right]
  exact hA'.tsum_add hD'

theorem operatorTrace_smul (c : ℂ) (A : E →L[ℂ] E) (hA : IsTraceClass A) :
    operatorTrace (c • A) = c * operatorTrace A := by
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))
  have hA' := (operatorTraceBasis E A _ b hA).1.of_norm
  change (∑' i, inner ℂ (b i) ((c • A) (b i))) =
    c * ∑' i, inner ℂ (b i) (A (b i))
  simp only [smul_apply, inner_smul_right]
  exact hA'.tsum_mul_left c

theorem operatorTraceLinearity : OperatorTraceLinearityStatement.{u} := by
  intro E _ _ _
  exact ⟨operatorTrace_zero, operatorTrace_add, operatorTrace_smul⟩

theorem operatorTraceCyclicity : OperatorTraceCyclicityStatement.{u, v} := by
  intro E F _ _ _ _ _ _ A B C hA
  have hF := isTraceClass_sandwich A B C hA
  have hE := isTraceClass_precomp A (C.comp B) hA
  refine ⟨hF, hE, ?_⟩
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ E
  obtain ⟨κ, d, _⟩ := exists_hilbertBasis ℂ F
  rw [(operatorTraceBasis F _ κ d hF).2, (operatorTraceBasis E _ ι b hE).2]
  obtain ⟨U, V, hU, hV, hfac⟩ := traceClassFactorization E A hA
  have hVC := isHilbertSchmidt_precomp V C hV
  have hBU := isHilbertSchmidt_postcomp U B hU
  have hVCB := isHilbertSchmidt_precomp V (C.comp B) hV
  have h₁ := hilbertSchmidtProductTrace F E κ ι (V.comp C) (B.comp U) d b hVC hBU
  have h₂ := hilbertSchmidtProductTrace E E ι ι (V.comp (C.comp B)) U b b hVCB hU
  have h₁' : traceIn d ((B.comp A).comp C) =
      traceIn b (V.comp (C.comp (B.comp U))) := by
    simpa only [hfac, ContinuousLinearMap.comp_assoc] using h₁.2.2
  have h₂' : traceIn b (A.comp (C.comp B)) =
      traceIn b (V.comp (C.comp (B.comp U))) := by
    simpa only [hfac, ContinuousLinearMap.comp_assoc] using h₂.2.2
  exact h₁'.trans h₂'.symm

theorem operatorTraceLaws : OperatorTraceLawsStatement.{u, v, w} := by
  exact ⟨operatorTraceBasis, operatorTraceLinearity, operatorTraceCyclicity⟩

end Langlands.Analysis.OperatorIdeals
