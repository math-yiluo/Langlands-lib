import Langlands.LocalFactor.Harmonic.Statement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Scalar p-adic Fourier scaling

The actual residue-normalized scalar Haar pushforward yields the image-set
modulus and the plus-sign Fourier substitution law. Measure and character
scaling follow directly from the Bochner integral and additive character APIs.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis

private theorem fourierIntegral_inv_eq_plus {K : Type*} [CommRing K]
    [MeasurableSpace K] (ψ : AddChar K Circle) (μ : Measure K)
    (f : K → ℂ) (y : K) :
    Fourier.fourierIntegral ψ⁻¹ μ f y = ∫ x, (ψ (x * y) : ℂ) * f x ∂μ := by
  simp only [Fourier.fourierIntegral_def, AddChar.inv_apply, neg_neg, Circle.smul_def, smul_eq_mul]

universe u

/-- All four scalar scaling laws with the supplied topology, Haar measure and
actual residue-normalized absolute value, with the exact published telescope. -/
theorem padicFourierScaling : LocalFactors.PadicFourierScalingStatement.{u} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ _ _ μ hμ
  let := hμ
  constructor
  · intro a s hs
    have hpre : (fun x : F.Carrier => (a⁻¹ : F.Carrierˣ) * x) ⁻¹' s =
        (fun x => (a : F.Carrier) * x) '' s := by
      ext x
      constructor
      · intro hx
        exact ⟨_, hx, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        change (↑a⁻¹ : F.Carrier) * ((a : F.Carrier) * z) ∈ s
        simpa only [← mul_assoc, Units.inv_mul, one_mul] using hz
    have h := congrArg (fun ν : Measure F.Carrier => ν s)
      (padicScalarHaarScaling F T μ a⁻¹)
    rw [Measure.map_apply (measurable_const_mul _) hs, hpre, Measure.smul_apply] at h
    simpa only [map_inv, Units.val_inv_eq_inv_val, inv_inv, ENNReal.smul_def,
      smul_eq_mul, ← T.normalizedAbsUnits_coe, ENNReal.ofReal_coe_nnreal] using h
  · intro f _ _
    refine ⟨?_, ?_, ?_⟩
    · intro c _ y
      simp only [fourierIntegral_inv_eq_plus, integral_smul_nnreal_measure,
        NNReal.smul_def, Complex.real_smul]
    · intro a y
      simp only [fourierIntegral_inv_eq_plus, AddChar.mulShift_apply]
      congr 1
      funext x
      rw [mul_left_comm (a : F.Carrier) x y]
    · intro a y
      let g : F.Carrier → ℂ := fun z =>
        (ψ (z * ((a⁻¹ : F.Carrierˣ) * y)) : ℂ) * f z
      have he : MeasurableEmbedding (fun x : F.Carrier => (a : F.Carrier) * x) :=
        (MeasurableEquiv.mulLeft₀ (a : F.Carrier) a.ne_zero).measurableEmbedding
      calc
        Fourier.fourierIntegral ψ⁻¹ μ (fun x => f ((a : F.Carrier) * x)) y =
            ∫ x, g ((a : F.Carrier) * x) ∂μ := by
          rw [fourierIntegral_inv_eq_plus]
          congr 1
          funext x
          simp only [g]
          congr 3
          simp [mul_assoc, mul_left_comm (a : F.Carrier) x]
        _ = ∫ z, g z ∂μ.map (fun x => (a : F.Carrier) * x) :=
          (he.integral_map g).symm
        _ = ∫ z, g z ∂((T.normalizedAbsUnits a : ℝ≥0)⁻¹ • μ) := by
          rw [padicScalarHaarScaling F T μ a]
        _ = _ := by
          rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
            NNReal.coe_inv, T.normalizedAbsUnits_coe, fourierIntegral_inv_eq_plus]

end Langlands.HarmonicAnalysis
