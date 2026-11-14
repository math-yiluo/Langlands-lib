import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
/-!
# Actual left-right changes of variables in the matrix Fourier pairing

Internal Fourier transport helpers for the matrix-to-rank-one comparison.
These results do not assert the matrix-to-Whittaker analytic passage.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

section Algebra


end Algebra

section ChangeOfVariables



end ChangeOfVariables

universe uF

/-- Determinant-norm-one left-right multiplication preserves every actual
rectangular additive Haar measure, including the empty-dimensional cases. -/
theorem padicRectangularLeftRight_measurePreserving
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (r s : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F)]
      [BorelSpace (Matrix (Fin r) (Fin s) F)]
      (μ : Measure (Matrix (Fin r) (Fin s) F)) [IsAddHaarMeasure μ]
      (A : GeneralLinear r F) (B : GeneralLinear s F),
      T.determinantNorm r A = 1 → T.determinantNorm s B = 1 →
      MeasurePreserving (fun X => A.val * X * B.val) μ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A B hA hB
  refine ⟨((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable,
    ?_⟩
  have h := padicRectangularHaarScaling F T r s μ A B⁻¹
  simpa only [inv_inv, map_inv, hA, hB, inv_one, Units.val_one, one_pow, div_one,
    one_smul] using h

/-- The plus transpose Fourier integral has no extra scalar under
determinant-norm-one left-right multiplication, for every supplied scalar Haar
measure and every character. -/
theorem padicRectangularFourierIntegral_leftRight
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (r s : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (A : GeneralLinear r F) (B : GeneralLinear s F),
      T.determinantNorm r A = 1 → T.determinantNorm s B = 1 →
      ∀ (Φ : Matrix (Fin r) (Fin s) F → ℂ)
        (X : Matrix (Fin r) (Fin s) F),
      rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X =
        rectangularFourierIntegral ψ ν Φ
          ((GeneralLinear.inverseTranspose r F A).val * X *
            (GeneralLinear.inverseTranspose s F B).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν A B hA hB Φ X
  have hm := (padicRectangularLeftRight_measurePreserving F T r s
    (RankinSelberg.rectangularMeasure ν r s) A B hA hB).map_eq
  have hm' : (RankinSelberg.rectangularMeasure ν r s).map
      (rectangularLeftRightHomeomorph A B) =
      (1 : ℝ≥0) • RankinSelberg.rectangularMeasure ν r s := by
    rw [one_smul]
    convert hm using 1
    rfl
  simpa only [NNReal.coe_one, Complex.ofReal_one, one_mul] using
    rectangularFourierIntegral_leftRight ψ ν A B 1 hm' Φ X

end Langlands.AllField.HarmonicAnalysis

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF

end Langlands.AllField.GodementJacquet
