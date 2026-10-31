import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Group.GL.Maps

/-!
# Rectangular Fourier integrals of two-sided unimodular translates

Two-sided multiplication by invertible matrices of normalized determinant one
preserves the rectangular product measure, and the raw plus-sign rectangular
Fourier integral of `x ↦ f (A * x * B)` at `y` is the Fourier integral of `f`
at `Aᵀ⁻¹ * y * Bᵀ⁻¹`. Elements of a compact subgroup of `GL_n` have normalized
determinant one.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory
open scoped NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

variable {r s : ℕ}

/-- Two-sided multiplication by matrices of normalized determinant one preserves
the rectangular product measure. -/
theorem measurePreserving_rectangular_mul_mul
    (ν : letI := T.topology; letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier)
    (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier)
    (hA : T.determinantNorm r A = 1) (hB : T.determinantNorm s B = 1) :
    letI := T.topology
    letI := borel F.Carrier
    MeasurePreserving (fun X : Matrix (Fin r) (Fin s) F.Carrier => A.val * X * B.val)
      (RankinSelberg.rectangularMeasure ν r s) (RankinSelberg.rectangularMeasure ν r s) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hmeas : Measurable (fun X : Matrix (Fin r) (Fin s) F.Carrier => A.val * X * B.val) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  refine ⟨hmeas, ?_⟩
  have h := padicRectangularHaarScaling F T r s (RankinSelberg.rectangularMeasure ν r s) A B⁻¹
  simp only [inv_inv, map_inv, hA, hB, Units.val_one, one_pow, inv_one, div_one,
    one_smul] at h
  exact h

/-- The rectangular pairing is invariant under `x ↦ A x B`, `y ↦ Aᵀ⁻¹ y Bᵀ⁻¹`. -/
theorem rectangularPairing_mul_mul (A : GeneralLinear r F.Carrier)
    (B : GeneralLinear s F.Carrier) (x y : Matrix (Fin r) (Fin s) F.Carrier) :
    rectangularPairing (A.val * x * B.val)
        ((GeneralLinear.inverseTranspose r F.Carrier A).val * y *
          (GeneralLinear.inverseTranspose s F.Carrier B).val) =
      rectangularPairing x y := by
  have htr (a b : Matrix (Fin r) (Fin s) F.Carrier) :
      rectangularPairing a b = Matrix.trace (a * b.transpose) := by
    simp only [rectangularPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply]
  rw [htr, htr]
  simp only [GeneralLinear.inverseTranspose_coe, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  have hB : B.val * (B⁻¹ : GeneralLinear s F.Carrier).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA : (A⁻¹ : GeneralLinear r F.Carrier).val * A.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc Matrix.trace (A.val * x * B.val *
        ((B⁻¹ : GeneralLinear s F.Carrier).val * (y.transpose *
          (A⁻¹ : GeneralLinear r F.Carrier).val)))
      = Matrix.trace (A.val * (x * y.transpose * (A⁻¹ : GeneralLinear r F.Carrier).val)) := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc B.val, hB, Matrix.one_mul]
    _ = Matrix.trace (x * y.transpose * (A⁻¹ : GeneralLinear r F.Carrier).val * A.val) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = Matrix.trace (x * y.transpose) := by
        rw [Matrix.mul_assoc, hA, Matrix.mul_one]

/-- The raw rectangular Fourier integral of a two-sided unimodular translate. -/
theorem rectangularFourierIntegral_comp_mul_mul
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := T.topology; letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier)
    (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier)
    (hA : T.determinantNorm r A = 1) (hB : T.determinantNorm s B = 1)
    (f : Matrix (Fin r) (Fin s) F.Carrier → ℂ) (y : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    letI := borel F.Carrier
    rectangularFourierIntegral ψ ν (fun x => f (A.val * x * B.val)) y =
      rectangularFourierIntegral ψ ν f
        ((GeneralLinear.inverseTranspose r F.Carrier A).val * y *
          (GeneralLinear.inverseTranspose s F.Carrier B).val) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hmp := measurePreserving_rectangular_mul_mul T ν A B hA hB
  have hA1 : (A⁻¹ : GeneralLinear r F.Carrier).val * A.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA2 : A.val * (A⁻¹ : GeneralLinear r F.Carrier).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB1 : B.val * (B⁻¹ : GeneralLinear s F.Carrier).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hB2 : (B⁻¹ : GeneralLinear s F.Carrier).val * B.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : Matrix (Fin r) (Fin s) F.Carrier ≃ₜ Matrix (Fin r) (Fin s) F.Carrier :=
    { toFun := fun X => A.val * X * B.val
      invFun := fun X => (A⁻¹ : GeneralLinear r F.Carrier).val * X *
        (B⁻¹ : GeneralLinear s F.Carrier).val
      left_inv := fun X => by
        simp only [Matrix.mul_assoc]
        rw [hB1, Matrix.mul_one, ← Matrix.mul_assoc, hA1, Matrix.one_mul]
      right_inv := fun X => by
        simp only [Matrix.mul_assoc]
        rw [hB2, Matrix.mul_one, ← Matrix.mul_assoc, hA2, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const }
  unfold rectangularFourierIntegral
  have h := hmp.integral_comp e.measurableEmbedding
    (fun z => f z * ψ.complex (rectangularPairing z
      ((GeneralLinear.inverseTranspose r F.Carrier A).val * y *
        (GeneralLinear.inverseTranspose s F.Carrier B).val)))
  rw [← h]
  congr 1
  funext x
  change f (A.val * x * B.val) * ψ.complex (rectangularPairing x y) =
    f (A.val * x * B.val) * ψ.complex (rectangularPairing (A.val * x * B.val) _)
  rw [rectangularPairing_mul_mul]

/-- A finite decomposition of a two-sided unimodular translate of a Schwartz
function transfers, with the same coefficients, to the Fourier integrals. -/
theorem rectangularFourierIntegral_translate_decomposition
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := T.topology; letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier)
    (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier)
    (hA : T.determinantNorm r A = 1) (hB : T.determinantNorm s B = 1)
    (Φ : letI := T.topology; SchwartzBruhat (Matrix (Fin r) (Fin s) F.Carrier))
    {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (Φs : ι → letI := T.topology; SchwartzBruhat (Matrix (Fin r) (Fin s) F.Carrier))
    (hdec : ∀ x, Φ (A.val * x * B.val) = ∑ l ∈ S, c l * Φs l x)
    (y : Matrix (Fin r) (Fin s) F.Carrier) :
    letI := T.topology
    letI := borel F.Carrier
    rectangularFourierIntegral ψ ν Φ
        ((GeneralLinear.inverseTranspose r F.Carrier A).val * y *
          (GeneralLinear.inverseTranspose s F.Carrier B).val) =
      ∑ l ∈ S, c l * rectangularFourierIntegral ψ ν (Φs l) y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  rw [← rectangularFourierIntegral_comp_mul_mul T ψ ν A B hA hB]
  unfold rectangularFourierIntegral
  simp_rw [hdec, Finset.sum_mul]
  rw [integral_finsetSum]
  · congr 1
    funext l
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro l _
    simp_rw [mul_assoc]
    exact (rectangularFourierIntegrand_integrable ψ ν (Φs l) y).const_mul _

end Langlands.HarmonicAnalysis
