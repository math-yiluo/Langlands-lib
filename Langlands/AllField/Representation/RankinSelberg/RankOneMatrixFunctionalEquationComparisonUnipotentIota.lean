import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Langlands.AllField.Representation.Induction.InverseTranspose
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
/-! Inverse-transpose and right-translate forms of the unipotent Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators NNReal Pointwise

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uG uK

end Langlands.AllField.RankinSelberg

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis

open Langlands.GeneralLinear

universe uK




end Langlands.AllField.HarmonicAnalysis

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis

open Langlands.GeneralLinear

universe uK

/-- The inverse-transpose identity with a determinant-norm-one right factor:
the Fourier side carries `h`, and the original side carries `h^iota`. The
supplied scalar Haar and the actual unipotent Haar are retained. -/
theorem padicUnipotentHaar_iota_fourier_duality_right
    (F : Type uK) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := RankinSelberg.localField_t2 F
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ [MeasurableSpace (upperUnipotent (n + 1) F)]
      [BorelSpace (upperUnipotent (n + 1) F)]
      (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      [SigmaFinite ν.measure], IsSelfDual ψ ν →
      ∀ (μ : Measure (upperUnipotent (n + 1) F))
        [μ.IsHaarMeasure] [μ.IsInvInvariant]
        (h : GeneralLinear (n + 1) F), T.determinantNorm (n + 1) h = 1 →
        ∀ Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F),
    Integrable (fun z : upperUnipotent (n + 1) F × F =>
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2 * h.val))
      (μ.prod ν.measure) ∧
    Integrable (fun z : upperUnipotent (n + 1) F × (Fin n → F) =>
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2 *
          (inverseTranspose (n + 1) F h).val))
      (μ.prod (rowMeasure ν n)) ∧
    (∫ z : upperUnipotent (n + 1) F × F,
      inverseUnipotentFourierPhase ψ n z.1 * rectangularFourierIntegral ψ ν Φ
        ((z.1⁻¹).val.val.transpose * cyclicShiftMatrix n z.2 * h.val)
      ∂μ.prod ν.measure) =
    ∫ z : upperUnipotent (n + 1) F × (Fin n → F),
      inverseUnipotentFourierPhase ψ n z.1 *
        Φ (z.1.val.val * firstColumnMatrix n z.2 *
          (inverseTranspose (n + 1) F h).val)
      ∂μ.prod (rowMeasure ν n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have : T2Space F := RankinSelberg.localField_t2 F
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro _ _ ψ ν _ hsd μ _ _ h hh Φ
  let hi := inverseTranspose (n + 1) F h
  have hhi : T.determinantNorm (n + 1) hi = 1 := by
    rw [T.determinantNorm_inverseTranspose, hh, inv_one]
  let Φh := rectangularLeftRightTranslate 1 hi Φ
  have hf (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
      rectangularFourierIntegral ψ ν Φh Y =
        rectangularFourierIntegral ψ ν Φ (Y * h.val) := by
    change rectangularFourierIntegral ψ ν (fun Y => Φ (1 * Y * hi.val)) Y = _
    simpa only [map_one, Units.val_one, Matrix.one_mul, hi,
      inverseTranspose_involutive] using
      padicRectangularFourierIntegral_leftRight F T (n + 1) (n + 1)
        ψ ν 1 hi (map_one _) hhi Φ Y
  have hb := unipotentHaar_iota_fourier_duality ψ ν hsd μ Φh
  simpa only [hf, Φh, rectangularLeftRightTranslate_apply, Units.val_one,
    Matrix.one_mul, hi] using hb

end Langlands.AllField.HarmonicAnalysis
