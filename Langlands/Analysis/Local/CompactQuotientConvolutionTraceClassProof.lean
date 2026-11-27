import Langlands.Analysis.Local.CompactQuotientConvolutionTraceClassStatement
import Langlands.Analysis.Local.CompactQuotientHilbertSchmidtProof
import Langlands.Analysis.HilbertSchmidtProductTraceClassProof
import Langlands.Representation.Unitary.IntegratedConvolutionProof

/-! # Trace-class products on a compact left coset space -/

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open Langlands.Analysis Langlands.Analysis.OperatorIdeals

/-- The convolution of two compactly supported continuous weights acts by a
product of Hilbert–Schmidt operators on the compact quotient, so its operator
is trace class (Getz–Hahn, Lemma 9.3.3, last step of the proof). -/
theorem compactQuotientConvolutionTraceClass :
    CompactQuotientConvolutionTraceClassStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ _ ν _ hν hcompact
    π hπnorm hπmeas hπapply f₁ f₂
  have hf₁ : Integrable f₁ μG := f₁.continuous.integrable_of_hasCompactSupport f₁.hasCompactSupport
  have hf₂ : Integrable f₂ μG := f₂.continuous.integrable_of_hasCompactSupport f₂.hasCompactSupport
  have hHS := compactQuotientIntegratedHilbertSchmidt H hH μH μG ν hν hcompact
    π hπnorm hπmeas hπapply
  obtain ⟨h, hcomp⟩ := integratedActionConvolution G (Lp ℂ 2 ν) μG π hπnorm hπmeas
    f₁ f₂ hf₁ hf₂
  refine ⟨h, ?_⟩
  rw [hcomp]
  exact hilbertSchmidtProductTraceClass _ _ _ _ (hHS f₂ hf₂) (hHS f₁ hf₁)

end Langlands.QuotientIntegration
