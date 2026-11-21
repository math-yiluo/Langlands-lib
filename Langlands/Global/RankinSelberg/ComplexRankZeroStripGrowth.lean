import Langlands.Global.RankinSelberg.ComplexRankZeroNormalization
import Langlands.Global.RankinSelberg.ComplexTateProductStripGrowth
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Automorphic.AssociatedGammaCuspidalEquation

/-! # Exponential strip growth for the complex rank-one ordinary local integral -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap Topology NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.LocalFactor.Archimedean ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

private def liftSchwartz (f : 𝓢(ℂ, ℂ)) : 𝓢(Fin 1 → ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ) f

private theorem scalar_zeta_eq_product (f : 𝓢(ℂ, ℂ)) (m : ℤ) (s : ℂ) :
    LocalFactor.ComplexTate.zeta f m s =
      2 * ComplexTateProduct.zeta (liftSchwartz f) (fun _ => m) (fun _ => s) := by
  unfold LocalFactor.ComplexTate.zeta LocalFactor.ComplexTate.measure ComplexTateProduct.zeta
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat]
  congr 1
  let G := ComplexTateProduct.integrand (liftSchwartz f) (fun _ => m) (fun _ => s)
  calc
    _ = ∫ z : ℂ, G (fun _ => z) ∂volume := by
      refine integral_congr_ae (.of_forall fun z => ?_)
      change LocalFactor.ComplexTate.integrand f m s z =
        ComplexTateProduct.integrand (liftSchwartz f) (fun _ => m) (fun _ => s) (fun _ => z)
      have hf : liftSchwartz f (fun _ => z) = f z := rfl
      rw [ComplexTateProduct.integrand, hf, Fin.prod_univ_one]
      by_cases hz : z = 0 <;> simp [LocalFactor.ComplexTate.integrand,
        LocalFactor.ComplexTate.direction, ComplexTateProduct.additiveWeight, hz, mul_assoc]
    _ = _ := (volume_preserving_funUnique (Fin 1) ℂ).symm.integral_comp' G

private theorem stripGrowth_const_mul {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (c : ℂ) :
    HasStripExponentialGrowth (fun s => c * f s) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hB⟩ := hf a b
  refine ⟨‖c‖ * C, K, T, by positivity, hK, fun s ha hb hs => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hB s ha hb hs) (norm_nonneg _)

/-- The entire scalar complex Tate normalization has exponential strip growth. -/
theorem stripGrowth_complex_normalizedZeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) :
    HasStripExponentialGrowth (LocalFactor.ComplexTate.normalizedZeta f m) := by
  obtain ⟨H, hH⟩ := ComplexTateProduct.complexTateProductEntireFamily 0
  let N (s : ℂ) : ℂ := 2 * H (liftSchwartz f) (fun _ => m) (fun _ => s)
  have hU (s : ℂ) : ComplexTateProduct.affineParameter (ι := Fin 1) (fun _ => 0) (fun _ => 1) s =
      fun _ => s := by
    funext j
    simp [ComplexTateProduct.affineParameter]
  have hG : HasStripExponentialGrowth N := by
    apply stripGrowth_const_mul (c := 2)
    simpa only [hU] using
      ComplexTateProduct.complexTateProductStripGrowth 0 H hH (liftSchwartz f) (fun _ => m)
        (fun _ => 0) (fun _ => 1)
  have hN : AnalyticOnNhd ℂ N univ := by
    intro s _
    have h := (hH.1 (liftSchwartz f) (fun _ => m) (fun _ => 0) (fun _ => 1)).const_mul (2 : ℂ)
    have hNdiff : Differentiable ℂ N := by
      simpa only [N, hU] using h
    exact hNdiff.analyticAt s
  have hZ : AnalyticOnNhd ℂ (LocalFactor.ComplexTate.normalizedZeta f m) univ :=
    fun s _ => LocalFactor.ComplexTate.analyticAt_normalizedZeta f m s
  have heq : LocalFactor.ComplexTate.normalizedZeta f m = N := by
    apply hZ.eq_of_eventuallyEq hN (z₀ := 1)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 0 < (1 : ℂ).re)]
      with s hs
    rw [LocalFactor.ComplexTate.normalizedZeta_eq_right _ _ hs, scalar_zeta_eq_product]
    dsimp only [N]
    rw [hH.2 _ _ _ (fun _ => hs), ComplexTateProduct.normalizedZeta, Fin.prod_univ_one,
      ComplexTateProduct.gammaNormalizer]
    ring
  rwa [heq]

private theorem zeta_shift (f : ℂ → ℂ) (m : ℤ) (t s : ℂ) :
    ComplexTate.zeta f m t s = LocalFactor.ComplexTate.zeta f m (s + t) := rfl

/-- The actual complex rank-one ordinary integral of two character coefficients has an
entire normalization of exponential strip growth. -/
def ComplexRankZeroStripGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData 0) (c c' : ComplexCharacterData)
    (W W' : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) (C C' : ℂ),
    (∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ)) →
    (∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ)) →
    ∀ Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ),
    ∃ N : OrdinaryIntegralNormalization (complexEqualIntegral D W W' Φ)
      (fun s => ((complexPairLFactor [c] [c']).denominator s)⁻¹), HasStripExponentialGrowth N.value

theorem complexRankZeroStripGrowth : ComplexRankZeroStripGrowthStatement := by
  intro D c c' W W' C C' hW hW' Φ
  obtain ⟨κ, _, hκ⟩ := exists_measure_eq D
  obtain ⟨τ, hτ⟩ := complexPairLFactor_denominator_ne_zero [c] [c']
  let d := c.mul c'
  let N (s : ℂ) := (κ : ℂ) / 2 * (C * C') *
    LocalFactor.ComplexTate.normalizedZeta (lineSchwartz Φ) d.weight (s + d.exponent)
  have hN (s : ℂ) : AnalyticAt ℂ N s := by
    have h := (LocalFactor.ComplexTate.analyticAt_normalizedZeta
      (lineSchwartz Φ) d.weight (s + d.exponent)).comp
      (f := fun w : ℂ => w + d.exponent) (x := s) (by fun_prop)
    exact analyticAt_const.fun_mul h
  have hG : HasStripExponentialGrowth N := by
    apply stripGrowth_const_mul
    simpa only [ofReal_one, div_one] using
      (stripGrowth_complex_normalizedZeta (lineSchwartz Φ) d.weight).div_add d.exponent
        (c := 1) one_pos
  refine ⟨⟨N, fun s _ => hN s, ⟨max τ (-d.exponent.re), fun s hs => ?_⟩⟩, hG⟩
  have hpos : 0 < (s + d.exponent).re := by
    rw [add_re]
    linarith [(le_max_right τ (-d.exponent.re)).trans_lt hs]
  have hD := hτ s ((le_max_left τ (-d.exponent.re)).trans_lt hs)
  have hEq : N s = complexEqualIntegral D W W' Φ s * (complexPairLFactor [c] [c']).denominator s := by
    dsimp only [N, d]
    rw [LocalFactor.ComplexTate.normalizedZeta_eq_right _ _ hpos,
      equalIntegral_eq c c' hκ hW hW', zeta_shift, complexPairLFactor_singleton, ← add_assoc]
    ring
  rw [hEq, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
