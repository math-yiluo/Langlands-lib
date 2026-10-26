import Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceStatement
import Langlands.HarmonicAnalysis.RowSchwartzAction
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# P-adic row Fourier equivariance under general linear substitutions

A general change of variables for the plus-sign row Fourier integral under
right multiplication by an invertible matrix, followed by its p-adic
specialization to the published statement.
-/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal

namespace Langlands.HarmonicAnalysis

section General

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] {d : ℕ}

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
/-- Right multiplication in the first argument of the row pairing becomes
right multiplication by the transpose in the second argument. -/
theorem rowPairing_vecMul (z y : Fin d → K) (A : Matrix (Fin d) (Fin d) K) :
    rowPairing (z ᵥ* A) y = rowPairing z (y ᵥ* Aᵀ) := by
  change (z ᵥ* A) ⬝ᵥ y = z ⬝ᵥ (y ᵥ* Aᵀ)
  rw [vecMul_transpose, dotProduct_mulVec]

variable [SecondCountableTopology K]

/-- A scalar change-of-variables character for `ν` gives the determinant
change of variables for right multiplication on the finite product measure. -/
theorem rowMeasure_map_vecMul (χ : K →*₀ ℝ≥0) (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure]
    (hχ : ∀ a : K, a ≠ 0 → ν.measure.map (fun x => a * x) = (χ a)⁻¹ • ν.measure)
    (g : GeneralLinear d K) :
    (rowMeasure ν d).map (fun x => x ᵥ* g.val) = (χ (det g.val))⁻¹ • rowMeasure ν d := by
  have hdet : det (g.val)ᵀ ≠ 0 := by
    rw [det_transpose]
    exact ((isUnit_iff_isUnit_det g.val).mp g.isUnit).ne_zero
  have h := productMeasure_map_matrix (ι := Fin d) ν.measure χ hχ hdet
  have he : (⇑(toLin' (g.val)ᵀ) : (Fin d → K) → Fin d → K) = fun x => x ᵥ* g.val := by
    funext x
    rw [toLin'_apply, mulVec_transpose]
  rw [he, det_transpose] at h
  exact h

/-- Change of variables for the row Fourier integral of an arbitrary function
under right multiplication by an invertible matrix. -/
theorem rowFourierIntegral_vecMul (χ : K →*₀ ℝ≥0) (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]
    (hχ : ∀ a : K, a ≠ 0 → ν.measure.map (fun x => a * x) = (χ a)⁻¹ • ν.measure)
    (g : GeneralLinear d K) (Φ : (Fin d → K) → ℂ) (y : Fin d → K) :
    rowFourierIntegral ψ ν d (fun x => Φ (x ᵥ* g.val)) y =
      ((((χ (det g.val) : ℝ≥0) : ℝ) : ℂ))⁻¹ *
        rowFourierIntegral ψ ν d Φ (y ᵥ* ((g⁻¹).val)ᵀ) := by
  have hL : MeasurableEmbedding (fun x : Fin d → K => x ᵥ* g.val) :=
    (rowHomeomorph g).measurableEmbedding
  let h : (Fin d → K) → ℂ := fun z => ψ.complex (rowPairing (z ᵥ* (g⁻¹).val) y) * Φ z
  calc rowFourierIntegral ψ ν d (fun x => Φ (x ᵥ* g.val)) y
      = ∫ x, h (x ᵥ* g.val) ∂rowMeasure ν d := by
        unfold rowFourierIntegral
        congr 1
        funext x
        simp only [h, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          vecMul_one]
    _ = ∫ z, h z ∂((rowMeasure ν d).map fun x => x ᵥ* g.val) := (hL.integral_map h).symm
    _ = ∫ z, h z ∂((χ (det g.val))⁻¹ • rowMeasure ν d) := by
        rw [rowMeasure_map_vecMul χ ν hχ g]
    _ = (χ (det g.val))⁻¹ • ∫ z, h z ∂rowMeasure ν d := integral_smul_nnreal_measure h _
    _ = _ := by
        rw [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv, Complex.ofReal_inv]
        unfold rowFourierIntegral
        congr 2
        funext z
        simp only [h, rowPairing_vecMul]

end General

universe uF

/-- Row Fourier equivariance under general linear substitutions, for every
supplied scalar Haar measure and every dimension, including zero. -/
theorem padicRowFourierEquivariance {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (d : ℕ) : PadicRowFourierEquivarianceStatement.{uF} F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ ν g Φ
  refine ⟨⟨rowTranslate g Φ, rowTranslate_apply g Φ⟩, fun Φg hΦg y => ?_⟩
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      ν.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.measure :=
    padicScalarHaarScaling F T ν.measure (Units.mk0 a ha)
  have hfun : (Φg : (Fin d → F.Carrier) → ℂ) = fun x => Φ (x ᵥ* g.val) := funext hΦg
  rw [hfun]
  exact rowFourierIntegral_vecMul T.normalizedAbsHom ψ ν hχ g Φ y

end Langlands.HarmonicAnalysis
