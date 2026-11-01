import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral

/-! Actual square-matrix Fourier exchange with a transpose and an arbitrary unit. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory
open scoped NNReal

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {d : ℕ}

/-- The transpose followed by right multiplication by a fixed matrix unit. -/
def squareTransposeRightHomeomorph (A : GeneralLinear d K) :
    Matrix (Fin d) (Fin d) K ≃ₜ Matrix (Fin d) (Fin d) K where
  toFun X := X.transpose * A.val
  invFun X := (X * (A⁻¹).val).transpose
  left_inv X := by
    change ((X.transpose * A.val) * (A⁻¹).val).transpose = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Matrix.transpose_transpose]
  right_inv X := by
    change (X * (A⁻¹).val).transpose.transpose * A.val = X
    rw [Matrix.transpose_transpose, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := continuous_id.matrix_transpose.matrix_mul continuous_const
  continuous_invFun := (continuous_id.matrix_mul continuous_const).matrix_transpose

@[simp] theorem squareTransposeRightHomeomorph_apply
    (A : GeneralLinear d K) (X : Matrix (Fin d) (Fin d) K) :
    squareTransposeRightHomeomorph A X = X.transpose * A.val := rfl

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

omit [IsTopologicalRing K] [BorelSpace K] [SecondCountableTopology K] in
/-- Fourier transform of a transposed test, for the exact product measure. -/
theorem rectangularFourierIntegral_transpose
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure]
    (Φ : Matrix (Fin d) (Fin d) K → ℂ) (X : Matrix (Fin d) (Fin d) K) :
    rectangularFourierIntegral ψ ν (fun Y => Φ Y.transpose) X =
      rectangularFourierIntegral ψ ν Φ X.transpose := by
  let e := GodementJacquet.transposeMeasurableEquiv (F := K) d d
  have hp := GodementJacquet.measurePreserving_transpose_rectangularMeasure ν d d
  have h := hp.integral_comp e.measurableEmbedding
    (fun Y => Φ Y * ψ.complex (rectangularPairing Y X.transpose))
  change (∫ Y, Φ Y.transpose * ψ.complex
    (rectangularPairing Y.transpose X.transpose) ∂RankinSelberg.rectangularMeasure ν d d) =
      _ at h
  simpa only [rectangularPairing_transpose, rectangularFourierIntegral] using h

end General

section Padic

/-- Transpose-right Fourier transport at every determinant norm, with the
Jacobian of the supplied additive product measure. -/
theorem padicSquareFourierIntegral_transposeRight
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (d : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier)
      (A : GeneralLinear d F.Carrier)
      (Φ : Matrix (Fin d) (Fin d) F.Carrier → ℂ)
      (X : Matrix (Fin d) (Fin d) F.Carrier),
    rectangularFourierIntegral ψ ν (fun Y => Φ (Y.transpose * A.val)) X =
      (((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ : ℝ≥0) *
        rectangularFourierIntegral ψ ν Φ
          (X.transpose * (GeneralLinear.inverseTranspose d F.Carrier A).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν A Φ X
  rw [rectangularFourierIntegral_transpose ψ ν (fun Y => Φ (Y * A.val))]
  have hm := padicRectangularHaarScaling F T d d
    (RankinSelberg.rectangularMeasure ν d d) 1 A⁻¹
  have hm' : (RankinSelberg.rectangularMeasure ν d d).map
      (rectangularLeftRightHomeomorph (1 : GeneralLinear d F.Carrier) A) =
      ((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ •
        RankinSelberg.rectangularMeasure ν d d := by
    change (RankinSelberg.rectangularMeasure ν d d).map
      (fun X => (1 : GeneralLinear d F.Carrier).val * X * A.val) = _
    simpa only [map_one, Units.val_one, Matrix.one_mul, inv_inv,
      map_inv, Units.val_inv_eq_inv_val, one_pow, inv_pow, one_div, inv_inv] using hm
  simpa only [Units.val_one, Matrix.one_mul, map_one] using
    rectangularFourierIntegral_leftRight ψ ν 1 A _ hm' Φ X.transpose

/-- Bilinear Fourier exchange with the actual transpose-right argument. The
determinant factor is present at arbitrary determinant norm. -/
theorem padicSquareFourierIntegral_crossExchange
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (d : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier)
      (A : GeneralLinear d F.Carrier)
      (Φ Ψ : SchwartzBruhat (Matrix (Fin d) (Fin d) F.Carrier)),
    (∫ X, rectangularFourierIntegral ψ ν Φ X * Ψ (X.transpose * A.val)
      ∂RankinSelberg.rectangularMeasure ν d d) =
      (((T.determinantNorm d A : ℝ≥0) ^ d)⁻¹ : ℝ≥0) *
        ∫ X, Φ X * rectangularFourierIntegral ψ ν Ψ
          (X.transpose * (GeneralLinear.inverseTranspose d F.Carrier A).val)
            ∂RankinSelberg.rectangularMeasure ν d d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
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

end Langlands.HarmonicAnalysis
