import Langlands.HarmonicAnalysis.SquareFourierCrossExchange
import Langlands.AllField.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
/-! Actual square-matrix Fourier exchange with a transpose and an arbitrary unit. -/

noncomputable section

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement measurePreserving_rectangular_mul_mul padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicSquareFourierIntegral_crossExchange padicSquareFourierIntegral_transposeRight rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis

open _root_.MeasureTheory
open scoped NNReal

universe uK uF

section General



end General

section Padic

/-- Transpose-right Fourier transport at every determinant norm, with the
Jacobian of the supplied additive product measure. -/
theorem padicSquareFourierIntegral_transposeRight
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (d : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F)
      (A : GeneralLinear d F)
      (Φ : Matrix (Fin d) (Fin d) F → ℂ)
      (X : Matrix (Fin d) (Fin d) F),
    rectangularFourierIntegral ψ ν (fun Y => Φ (Y.transpose * A.val)) X =
      (((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ : ℝ≥0) *
        rectangularFourierIntegral ψ ν Φ
          (X.transpose * (GeneralLinear.inverseTranspose d F A).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν A Φ X
  rw [rectangularFourierIntegral_transpose ψ ν (fun Y => Φ (Y * A.val))]
  have hm := padicRectangularHaarScaling F T d d
    (RankinSelberg.rectangularMeasure ν d d) 1 A⁻¹
  have hm' : (RankinSelberg.rectangularMeasure ν d d).map
      (rectangularLeftRightHomeomorph (1 : GeneralLinear d F) A) =
      ((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ •
        RankinSelberg.rectangularMeasure ν d d := by
    change (RankinSelberg.rectangularMeasure ν d d).map
      (fun X => (1 : GeneralLinear d F).val * X * A.val) = _
    simpa only [map_one, Units.val_one, Matrix.one_mul, inv_inv,
      map_inv, Units.val_inv_eq_inv_val, one_pow, inv_pow, one_div, inv_inv] using hm
  simpa only [Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_leftRight ψ ν 1 A _ hm' Φ X.transpose

/-- Bilinear Fourier exchange with the actual transpose-right argument. The
determinant factor is present at arbitrary determinant norm. -/
theorem padicSquareFourierIntegral_crossExchange
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (d : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F := borel F
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F)
      (A : GeneralLinear d F)
      (Φ Ψ : SchwartzBruhat (Matrix (Fin d) (Fin d) F)),
    (∫ X, rectangularFourierIntegral ψ ν Φ X * Ψ (X.transpose * A.val)
      ∂RankinSelberg.rectangularMeasure ν d d) =
      (((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ : ℝ≥0) *
        ∫ X, Φ X * rectangularFourierIntegral ψ ν Ψ
          (X.transpose * (GeneralLinear.inverseTranspose d F A).val)
            ∂RankinSelberg.rectangularMeasure ν d d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν A Φ Ψ
  let ΨA := Hecke.TestFunction.pullback (squareTransposeRightHomeomorph A) Ψ
  have he := (rectangularFourierIntegral_exchange ψ ν Φ ΨA).2.2
  change (∫ X, rectangularFourierIntegral ψ ν Φ X * Ψ (X.transpose * A.val)
      ∂RankinSelberg.rectangularMeasure ν d d) =
    ∫ X, Φ X * rectangularFourierIntegral ψ ν
      (fun Y => Ψ (Y.transpose * A.val)) X
        ∂RankinSelberg.rectangularMeasure ν d d at he
  rw [he]
  simp_rw [padicSquareFourierIntegral_transposeRight F T d ψ ν A Ψ,
    mul_left_comm (Φ _)]
  exact integral_const_mul _ _

end Padic

end Langlands.AllField.HarmonicAnalysis
