import Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureStatement
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# The JPSS rectangular character-change Haar law
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis
open scoped NNReal ENNReal

universe uF

private def characterChangeRowDiagonal {F : Type uF} [Field F] (a : Fˣ) (j : ℕ) :
    GeneralLinear j F where
  val := Matrix.diagonal fun i => (((a ^ (i.val + 1))⁻¹ : Fˣ) : F)
  inv := Matrix.diagonal fun i => ((a ^ (i.val + 1) : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

private theorem characterChangeRowDiagonal_det {F : Type uF} [Field F]
    (a : Fˣ) (j : ℕ) :
    GeneralLinear.determinant (characterChangeRowDiagonal a j) =
      (a ^ (∑ i : Fin j, (i.val + 1)))⁻¹ := by
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin j =>
    (((a ^ (i.val + 1))⁻¹ : Fˣ) : F))).det = _
  simp only [Matrix.det_diagonal, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]

private theorem characterChangeRowDiagonal_mul {F : Type uF} [Field F]
    (a : Fˣ) (j n : ℕ) :
    (fun X : Matrix (Fin j) (Fin (n + 1)) F =>
      (characterChangeRowDiagonal a j : Matrix (Fin j) (Fin j) F) * X) =
        characterChangeRectangular a j n := by
  funext X i l
  exact Matrix.diagonal_mul _ X i l

private theorem characterChangeRowDiagonal_modulus {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (a : F.Carrierˣ) (j n : ℕ) :
    ((T.determinantNorm j (characterChangeRowDiagonal a j) : ℝ≥0) ^ (n + 1))⁻¹ =
      characterChangeRectangularModulus (normalizedAbsoluteValue T) a j n := by
  change ((T.normalizedAbsUnits
    (GeneralLinear.determinant (characterChangeRowDiagonal a j)) : ℝ≥0) ^ (n + 1))⁻¹ = _
  rw [characterChangeRowDiagonal_det, map_inv, map_pow,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow, inv_inv, ← pow_mul]
  apply NNReal.eq
  simp only [NNReal.coe_pow, PadicField.TopologicalData.normalizedAbsUnits_coe]
  change T.normalizedAbs a ^ ((∑ i : Fin j, (i.val + 1)) * (n + 1)) =
    T.normalizedAbs a ^ ((n + 1) * ∑ i : Fin j, (i.val + 1))
  rw [Nat.mul_comm]

/-- The inverse row map has the positive JPSS modulus for every Borel additive Haar measure. -/
theorem characterChangeRectangularHaarStatement : CharacterChangeRectangularHaarStatement.{uF} := by
  intro p _ F T j n
  let := T.topology
  intro _ _ ν _ a
  have h := padicRectangularHaarScaling F T j (n + 1) ν
    (characterChangeRowDiagonal a j) 1
  simp only [map_one, Units.val_one, one_pow, div_one, inv_one, Matrix.mul_one] at h
  rw [characterChangeRowDiagonal_mul, characterChangeRowDiagonal_modulus] at h
  exact h

/-- The same law for the existing nested product of any shared scalar additive Haar measure. -/
theorem characterChangeRectangularProductStatement :
    CharacterChangeRectangularProductStatement.{uF} := by
  intro p _ F T j n
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro η a
  exact characterChangeRectangularHaarStatement p F T j n
    (rectangularMeasure η j (n + 1)) a

/-- The exact published general-then-product rectangular character-change proposition. -/
theorem characterChangeRectangularMeasureStatement :
    CharacterChangeRectangularMeasureStatement.{uF} :=
  ⟨characterChangeRectangularHaarStatement, characterChangeRectangularProductStatement⟩

end Langlands.RankinSelberg
