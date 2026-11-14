import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceStatement
/-!
# P-adic row Fourier equivariance under general linear substitutions

A general change of variables for the plus-sign row Fourier integral under
right multiplication by an invertible matrix, followed by its p-adic
specialization to the published statement.
-/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

section General



end General

universe uF

/-- Row Fourier equivariance under general linear substitutions, for every
supplied scalar Haar measure and every dimension, including zero. -/
theorem padicRowFourierEquivariance (F : Type uF) [Field F]
    (T : LocalFieldData F) (d : ℕ) : PadicRowFourierEquivarianceStatement.{uF} F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν g Φ
  refine ⟨⟨rowTranslate g Φ, rowTranslate_apply g Φ⟩, fun Φg hΦg y => ?_⟩
  have hχ (a : F) (ha : a ≠ 0) :
      ν.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.measure :=
    padicScalarHaarScaling F T ν.measure (Units.mk0 a ha)
  have hfun : (Φg : (Fin d → F) → ℂ) = fun x => Φ (x ᵥ* g.val) := funext hΦg
  rw [hfun]
  exact rowFourierIntegral_vecMul T.normalizedAbsHom ψ ν hχ g Φ y

end Langlands.AllField.HarmonicAnalysis
