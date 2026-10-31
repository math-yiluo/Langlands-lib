import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.Representation.GodementJacquet.AnalyticData

/-!
# Actual left-right changes of variables in the matrix Fourier pairing

Internal Fourier transport helpers for the matrix-to-rank-one comparison.
These results do not assert the matrix-to-Whittaker analytic passage.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal

namespace Langlands.HarmonicAnalysis

section Algebra

variable {K : Type*} [Field K] {r s : ℕ}

/-- Transposition preserves the entry pairing. -/
theorem rectangularPairing_transpose (Y X : Matrix (Fin r) (Fin s) K) :
    rectangularPairing Y.transpose X.transpose = rectangularPairing Y X := by
  exact Finset.sum_comm

/-- Right multiplication moves to the other argument by transposition. -/
theorem rectangularPairing_mul_right
    (Y X : Matrix (Fin r) (Fin s) K) (B : Matrix (Fin s) (Fin s) K) :
    rectangularPairing (Y * B) X = rectangularPairing Y (X * B.transpose) := by
  simp only [rectangularPairing, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Left multiplication moves to the other argument by transposition. -/
theorem rectangularPairing_mul_left
    (A : Matrix (Fin r) (Fin r) K) (Y X : Matrix (Fin r) (Fin s) K) :
    rectangularPairing (A * Y) X = rectangularPairing Y (A.transpose * X) := by
  calc
    _ = rectangularPairing (A * Y).transpose X.transpose :=
      (rectangularPairing_transpose _ _).symm
    _ = rectangularPairing Y.transpose (X.transpose * A) := by
      rw [Matrix.transpose_mul, rectangularPairing_mul_right, Matrix.transpose_transpose]
    _ = _ := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        rectangularPairing_transpose Y (A.transpose * X)

end Algebra

section ChangeOfVariables

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {r s : ℕ}

/-- Actual left-right multiplication, with its continuous inverse. -/
def rectangularLeftRightHomeomorph (A : GeneralLinear r K) (B : GeneralLinear s K) :
    Matrix (Fin r) (Fin s) K ≃ₜ Matrix (Fin r) (Fin s) K where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    change (A⁻¹).val * (A.val * X * B.val) * (B⁻¹).val = X
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv X := by
    change A.val * ((A⁻¹).val * X * (B⁻¹).val) * B.val = X
    simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

@[simp] theorem rectangularLeftRightHomeomorph_apply
    (A : GeneralLinear r K) (B : GeneralLinear s K) (X : Matrix (Fin r) (Fin s) K) :
    rectangularLeftRightHomeomorph A B X = A.val * X * B.val := rfl

/-- Pullback of actual Schwartz tests by left-right multiplication. -/
def rectangularLeftRightTranslate (A : GeneralLinear r K) (B : GeneralLinear s K) :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin s) K) :=
  Hecke.TestFunction.pullback (rectangularLeftRightHomeomorph A B)

@[simp] theorem rectangularLeftRightTranslate_apply
    (A : GeneralLinear r K) (B : GeneralLinear s K)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (X : Matrix (Fin r) (Fin s) K) :
    rectangularLeftRightTranslate A B Φ X = Φ (A.val * X * B.val) := rfl

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- The raw Fourier change of variables retains exactly the scalar by which
the actual product measure is pushed forward. No integrability assumption on
the input function is necessary. -/
theorem rectangularFourierIntegral_leftRight
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (A : GeneralLinear r K) (B : GeneralLinear s K) (c : ℝ≥0)
    (hmap : (RankinSelberg.rectangularMeasure ν r s).map
        (rectangularLeftRightHomeomorph A B) =
      c • RankinSelberg.rectangularMeasure ν r s)
    (Φ : Matrix (Fin r) (Fin s) K → ℂ) (X : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X =
      ((c : ℝ) : ℂ) * rectangularFourierIntegral ψ ν Φ
        ((GeneralLinear.inverseTranspose r K A).val * X *
          (GeneralLinear.inverseTranspose s K B).val) := by
  let e := rectangularLeftRightHomeomorph A B
  let h := fun Z : Matrix (Fin r) (Fin s) K =>
    Φ Z * ψ.complex (rectangularPairing (e.symm Z) X)
  calc
    _ = ∫ Y, h (e Y) ∂RankinSelberg.rectangularMeasure ν r s := by
      unfold rectangularFourierIntegral
      congr 1
      funext Y
      simp only [h, e.symm_apply_apply]
      rfl
    _ = ∫ Z, h Z ∂(RankinSelberg.rectangularMeasure ν r s).map e :=
      (e.measurableEmbedding.integral_map h).symm
    _ = c • ∫ Z, h Z ∂RankinSelberg.rectangularMeasure ν r s := by
      rw [hmap, integral_smul_nnreal_measure]
    _ = _ := by
      rw [NNReal.smul_def, Complex.real_smul]
      congr 1
      unfold rectangularFourierIntegral
      congr 1
      funext Z
      change Φ Z * ψ.complex
        (rectangularPairing ((A⁻¹).val * Z * (B⁻¹).val) X) = _
      rw [rectangularPairing_mul_right, rectangularPairing_mul_left, Matrix.mul_assoc]
      rfl

end ChangeOfVariables

universe uF

/-- Determinant-norm-one left-right multiplication preserves every actual
rectangular additive Haar measure, including the empty-dimensional cases. -/
theorem padicRectangularLeftRight_measurePreserving
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (r s : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      (μ : Measure (Matrix (Fin r) (Fin s) F.Carrier)) [IsAddHaarMeasure μ]
      (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier),
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
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (r s : ℕ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier),
      T.determinantNorm r A = 1 → T.determinantNorm s B = 1 →
      ∀ (Φ : Matrix (Fin r) (Fin s) F.Carrier → ℂ)
        (X : Matrix (Fin r) (Fin s) F.Carrier),
      rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X =
        rectangularFourierIntegral ψ ν Φ
          ((GeneralLinear.inverseTranspose r F.Carrier A).val * X *
            (GeneralLinear.inverseTranspose s F.Carrier B).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
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

end Langlands.HarmonicAnalysis

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uF

/-- Actual paired full-matrix Fourier tests are transported by left-right
determinant-norm-one changes and their inverse transposes, with the same
supplied measure and character. -/
theorem padicMatrixFourierPair_leftRight
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
      (A B : GeneralLinear (n + 1) F.Carrier),
      T.determinantNorm (n + 1) A = 1 → T.determinantNorm (n + 1) B = 1 →
      ∀ Φ ΦHat : MatrixTestFunction n F.Carrier,
      MatrixFourierPair ψ ν Φ ΦHat →
      MatrixFourierPair ψ ν (rectangularLeftRightTranslate A B Φ)
        (rectangularLeftRightTranslate
          (GeneralLinear.inverseTranspose (n + 1) F.Carrier A)
          (GeneralLinear.inverseTranspose (n + 1) F.Carrier B) ΦHat) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν A B hA hB Φ ΦHat hΦ X
  refine ⟨rectangularFourierIntegrand_integrable ψ ν _ X, ?_⟩
  rw [rectangularLeftRightTranslate_apply, (hΦ _).2]
  exact (padicRectangularFourierIntegral_leftRight F T (n + 1) (n + 1)
    ψ ν A B hA hB Φ X).symm

end Langlands.GodementJacquet
