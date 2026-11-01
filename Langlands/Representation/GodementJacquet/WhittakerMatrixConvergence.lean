import Langlands.Representation.GodementJacquet.WhittakerMatrixRationality
import Langlands.Representation.GodementJacquet.WhittakerSliceBound

/-!
# Convergence of full-matrix Whittaker integrals

Given `FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
full-matrix test function `Φ`, the integral `∫ Φ(g) W(g) |det g|^s dg` converges
absolutely on a right half-plane. The proof uses Iwasawa integration, the finite
coset sum over `K`, the unipotent volume bound, and the torus Mellin integrals.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixConvergenceTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance matrixConvergenceValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance matrixConvergenceLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance matrixConvergenceUnitsMeasurableSpace : MeasurableSpace F.Carrierˣ := borel _
local instance matrixConvergenceUnitsBorelSpace : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance matrixConvergenceMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance matrixConvergenceBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance matrixConvergenceUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance matrixConvergenceUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-! ### The torus weight `δ(a)⁻¹ ∏ |a_i|^(-e_i)` -/

/-- The weight `δ(a)⁻¹ ∏ |a_i|^(-e_i)` as a complex function on the torus. -/
def torusWeight (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → F.Carrierˣ) : ℂ :=
  (((borelModulus F a)⁻¹ * torusMonomial F e a : ℝ) : ℂ)

theorem torusWeight_mul (e : Fin (n + 1) → ℕ) (a b : Fin (n + 1) → F.Carrierˣ) :
    torusWeight F e (a * b) = torusWeight F e a * torusWeight F e b := by
  simp only [torusWeight, torusMonomial, borelModulus_mul, Pi.mul_apply, Units.val_mul,
    F.canonicalTopologicalData.normalizedAbs_mul, mul_inv, mul_pow, Finset.prod_mul_distrib]
  push_cast
  ring

theorem continuous_torusWeight (e : Fin (n + 1) → ℕ) : Continuous (torusWeight F e) := by
  refine Complex.continuous_ofReal.comp (((continuous_borelModulus F).inv₀
    fun a => (borelModulus_pos F a).ne').mul ?_)
  refine continuous_finsetProd _ fun i _ => Continuous.pow ?_ _
  exact (F.canonicalTopologicalData.continuous_normalizedAbs.comp
    (Units.continuous_val.comp (continuous_apply i))).inv₀
      fun a => (F.canonicalTopologicalData.normalizedAbs_pos (a i).ne_zero).ne'

theorem isFiniteFunction_torusWeight (e : Fin (n + 1) → ℕ) :
    IsFiniteFunction (torusWeight F e) :=
  IsFiniteFunction.of_mul_apply (continuous_torusWeight F e) (torusWeight F e)
    fun b a => torusWeight_mul F e b a

theorem enorm_torusWeight (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → F.Carrierˣ) :
    ‖torusWeight F e a‖ₑ =
      ENNReal.ofReal ((borelModulus F a)⁻¹) * ENNReal.ofReal (torusMonomial F e a) := by
  have hδ : 0 ≤ (borelModulus F a)⁻¹ := (inv_pos.2 (borelModulus_pos F a)).le
  rw [torusWeight, ← ofReal_norm,
    Complex.norm_of_nonneg (mul_nonneg hδ (torusMonomial_nonneg F e a)),
    ENNReal.ofReal_mul hδ]

/-! ### Convergence -/

/-- For `k ∈ K`, the torus integral of the unipotent integral of the matrix
integrand at `u diag(a) k` is finite on a right half-plane. -/
theorem lintegral_torus_lt_top (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F.Carrier) {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralK F n) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) < ⊤ := by
  obtain ⟨B, ρ, hρ, e, hslice⟩ := exists_slice_bound F Φ k
  obtain ⟨X, hX, φ, hφ⟩ := hW.expansion k
  let J := boxTest F n hρ
  obtain ⟨c, hc⟩ := exists_common_halfPlane X
    (fun χ s => Integrable (torusIntegrand F (φ χ) J (χ * torusWeight F e) s)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier))
    fun χ hχ => (torusMellin F hFFM _ ((hX χ hχ).mul (isFiniteFunction_torusWeight F e))
      (φ χ) J).1
  refine ⟨c, fun s hs => ?_⟩
  have hint := hc s hs
  have hpt : ∀ a : Fin (n + 1) → F.Carrierˣ,
      ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n ≤
        ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
    intro a
    rw [lintegral_unipotent_matrixIntegrand F hW.equivariant Φ s a hk]
    have hsum : W (Iwasawa.diagonalUnits a * k) *
        (J (fun i => (a i : F.Carrier)) * torusWeight F e a *
          ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s) =
        ∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a := by
      rw [show W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a from hφ a,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, Pi.mul_apply]
      ring
    calc ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ *
          ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ
            ∂unipotentHaar F.Carrier n)
        ≤ ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s‖ₑ *
          (ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F e a) *
            ‖J (fun i => (a i : F.Carrier))‖ₑ)) := by
          gcongr
          exact hslice a
      _ = ENNReal.ofReal B * ‖W (Iwasawa.diagonalUnits a * k) *
          (J (fun i => (a i : F.Carrier)) * torusWeight F e a *
            ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^
              s)‖ₑ := by
          simp only [enorm_mul]
          rw [enorm_torusWeight]
          ring
      _ = ENNReal.ofReal B *
          ‖∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          rw [hsum]
      _ ≤ ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          gcongr
          exact enorm_sum_le _ _
  calc ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)
      ≤ ∫⁻ a, ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * ∑ χ ∈ X, ∫⁻ a, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun χ hχ => (hint χ hχ).aestronglyMeasurable.enorm]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun χ hχ =>
        hasFiniteIntegral_iff_enorm.1 (hint χ hχ).hasFiniteIntegral)

/-- **Convergence of full-matrix Whittaker integrals.** Given
`FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
full-matrix test function `Φ`, the unshifted matrix integral
`∫ Φ(g) W(g) |det g|^s dg` converges absolutely for `Re s` large. -/
theorem IsWhittakerLike.matrixConverges (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F.Carrier) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → GodementJacquet.Padic.MatrixConverges F Φ s W := by
  obtain ⟨K₀, S, hK₀K, hSK, hinv, hlin, -⟩ := IsWhittakerLike.exists_cosetSum F hW Φ
  obtain ⟨c, hc⟩ := exists_common_halfPlane S
    (fun k s => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) < ⊤)
    fun k hk => lintegral_torus_lt_top F hFFM hW Φ (hSK hk)
  refine ⟨c, fun s hs => ?_⟩
  have hmeas := measurable_matrixIntegrand F hW.continuous Φ s
  change Integrable (GodementJacquet.Padic.matrixIntegrand F Φ s W) (generalLinearHaar F.Carrier n)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_iwasawa F _ hmeas.enorm,
    hlin (fun k => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F.Carrier n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier))
      fun k _ k₀ hk₀ => ?_]
  · refine ENNReal.sum_lt_top.2 fun k hk => ENNReal.mul_lt_top ?_ (hc s hs k hk)
    exact (measure_mono fun x hx => hK₀K hx).trans_lt
      ((generalLinearHaar_integralSubgroup F.Carrier n).trans_lt ENNReal.one_lt_top)
  · refine lintegral_congr fun a => ?_
    congr 1
    refine lintegral_congr fun u => ?_
    rw [← mul_assoc, hinv s _ k₀ hk₀]

end Padic

end Langlands.GodementJacquet.WhittakerTorus
