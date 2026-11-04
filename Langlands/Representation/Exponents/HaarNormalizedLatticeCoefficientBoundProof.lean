import Langlands.Representation.Exponents.HaarNormalizedLatticeCoefficientBoundStatement
import Langlands.Representation.Exponents.NormalizedJacquetCompressionSpectrumProof
import Langlands.Representation.Exponents.CompressedLatticeCoefficientBoundProof

/-! # Actual normalized Jacquet spectra give Haar-weighted coefficient decay -/

noncomputable section

open scoped NNReal

namespace Langlands

universe uG uV uI

namespace HaarNormalizedLatticeBound

/-- The square norm of the canonical inverse half is the inverse of the
original positive modulus. -/
theorem norm_inverseHalfCharacter_sq {H : Type*} [Group H]
    (δ : H →* ℝ≥0ˣ) (h : H) :
    ‖(Jacquet.inverseHalfCharacter δ h : ℂ)‖ ^ 2 = (((δ h : ℝ≥0) : ℝ))⁻¹ := by
  have he := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) (Jacquet.inverseHalfCharacter_sq δ h)
  simpa only [Units.val_pow_eq_pow_val, norm_pow, Units.val_inv_eq_inv_val,
    norm_inv, Jacquet.complexCharacter_apply, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using he

end HaarNormalizedLatticeBound

/-- Finite lattice coefficient decay compatible with the inverse actual Haar
modulus follows from strict actual normalized Jacquet exponents. -/
theorem haarNormalizedLatticeCoefficientBound :
    HaarNormalizedLatticeCoefficientBoundStatement.{uG, uV, uI} := by
  intro G _ _ _ _ I _ _ A hA K hK N₀ M₀ Nbar₀ hfactor τ hup hlow hmid
    N M Nbar hN hMN hbasis z hgen hcon hstrict v φ hφ
  let q : I → ℂ := fun i =>
    (HaarModulus.closedInverseHalfCharacter (N i) (hN i) (M i) (hMN i) (z i : M i) : ℂ)
  have hq : ∀ i, 0 < ‖q i‖ := fun i => norm_pos_iff.mpr (Units.ne_zero _)
  have hev : ∀ i (μ : ℂ) (x : fixedVectors A.representation K.toSubgroup), x ≠ 0 →
      Jacquet.compressedAction A.representation hA.1 K hK
        (τ (.ofAdd (Pi.single i 1))) x = μ • x → ‖μ‖ < ‖q i‖⁻¹ := by
    intro i μ x hx hμ
    rw [hgen i] at hμ
    have he := normalizedJacquetCompressionSpectrum G (N i) (M i) (Nbar i)
      (hN i) (hMN i) (hbasis i) A hA K hK (z i) (hcon i) (hstrict i) μ x hx hμ
    change ‖q i * μ‖ < 1 at he
    rw [norm_mul] at he
    simpa only [mul_one] using (lt_inv_mul_iff₀ (hq i)).mpr he
  obtain ⟨a, ha, C, hC, hbound⟩ := compressedLatticeCoefficientBound G A I
    A.representation hA K hK N₀ M₀ Nbar₀ hfactor τ hup hlow hmid
    (fun i => ‖q i‖⁻¹) (fun i => inv_pos.mpr (hq i)) hev v φ hφ
  refine ⟨a, fun i => ⟨(ha i).1, ?_⟩, C, hC, hbound⟩
  have hw : ‖q i‖ ^ 2 =
      (((HaarModulus.closedRestrictCharacter (N i) (hN i) (M i) (hMN i)
        (z i : M i) : ℝ≥0) : ℝ))⁻¹ :=
    HaarNormalizedLatticeBound.norm_inverseHalfCharacter_sq _ _
  rw [← hw, ← mul_pow]
  have hlt : a i * ‖q i‖ < 1 := (lt_inv_mul_iff₀' (hq i)).mp
    (by simpa only [mul_one] using (ha i).2)
  have hpos : 0 < a i * ‖q i‖ := mul_pos (ha i).1 (hq i)
  nlinarith

end Langlands
