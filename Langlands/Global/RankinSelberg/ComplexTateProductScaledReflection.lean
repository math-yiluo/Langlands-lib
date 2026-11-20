import Langlands.Global.RankinSelberg.ComplexTateProductEntireReflection
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Normalized product Tate reflection for a scaled complex trace character -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap Topology

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open ArchimedeanLocal
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.LocalFactor.Archimedean
open Langlands.LocalFactor.ComplexTate (direction direction_mul direction_ne_zero)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

local notation "V" => Fin (n + 1) → ℂ
local notation "W" => Fin (n + 1) → ℤ

private def scalarDilation (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ)) a).restrictScalars ℝ

private def vectorDilation (a : ℂˣ) : V ≃L[ℝ] V :=
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := V)) a).restrictScalars ℝ

private theorem vectorDilation_apply (a : ℂˣ) (x : V) (j : Fin (n + 1)) :
    vectorDilation a x j = (a : ℂ) * x j := rfl

private def dilate (a : ℂˣ) (F : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (vectorDilation a) F

private def density (a : ℂˣ) : ℝ≥0 := (‖(a : ℂ)‖₊ ^ 2)⁻¹

private theorem map_scalarDilation (a : ℂˣ) :
    (volume : Measure ℂ).map (scalarDilation a) = density a • (volume : Measure ℂ) := by
  let L := (scalarDilation a).toLinearEquiv.toLinearMap
  have hL : L = Algebra.lmul ℝ ℂ (a : ℂ) := by
    ext x
    rfl
  have hdet : L.det = ‖(a : ℂ)‖ ^ 2 := by
    rw [hL, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.sq_norm]
  have hpos : 0 < ‖(a : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr a.ne_zero) _
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := L) (hdet.trans_ne hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  rw [← Measure.coe_nnreal_smul, ← ENNReal.ofReal_coe_nnreal]
  exact h

private theorem integral_vectorDilation (a : ℂˣ) (f : V → ℂ) :
    (∫ x, f (vectorDilation a x)) = ((density a : ℝ) ^ (n + 1)) • ∫ x, f x := by
  let e : V ≃ᵐ V := (vectorDilation a).toHomeomorph.toMeasurableEquiv
  let p := (scalarDilation a).toHomeomorph.toMeasurableEquiv
  have hm : (volume : Measure V).map e = density a ^ (n + 1) • (volume : Measure V) := by
    change (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℂ))).map
      (fun (x : V) j => p (x j)) = _
    rw [Measure.pi_map_pi (hμ := fun _ => p.sigmaFinite_map) (fun _ => p.measurable.aemeasurable)]
    simp_rw [show (volume : Measure ℂ).map p = _ from map_scalarDilation a]
    rw [Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  calc
    (∫ x, f (vectorDilation a x)) = ∫ y, f y ∂(volume : Measure V).map e :=
      (integral_map_equiv (μ := (volume : Measure V)) e f).symm
    _ = _ := by rw [hm, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow]

private theorem additiveWeight_mul (a : ℂˣ) (m : ℤ) (u z : ℂ) :
    additiveWeight m u ((a : ℂ) * z) =
      (direction (a : ℂ) ^ m * (‖(a : ℂ)‖ : ℂ) ^ (2 * u - 2)) * additiveWeight m u z := by
  by_cases hz : z = 0
  · simp [additiveWeight, hz]
  simp only [additiveWeight, ite_eq_right hz, ite_eq_right (mul_ne_zero a.ne_zero hz)]
  change direction ((a : ℂ) * z) ^ m * (‖(a : ℂ) * z‖ : ℂ) ^ (2 * u - 2) =
    (direction (a : ℂ) ^ m * (‖(a : ℂ)‖ : ℂ) ^ (2 * u - 2)) *
      (direction z ^ m * (‖z‖ : ℂ) ^ (2 * u - 2))
  rw [direction_mul, mul_zpow, norm_mul, ofReal_mul,
    mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

private def dilationFactor (a : ℂˣ) (m : W) (u : V) : ℂ :=
  ∏ j, direction (a : ℂ) ^ (-m j) * (‖(a : ℂ)‖ : ℂ) ^ (-2 * u j)

private theorem normalizedZeta_dilate_smul (a : ℂˣ) (k : ℂ) (F : 𝓢(V, ℂ)) (m : W) (u : V) :
    normalizedZeta (k • dilate a F) m u = k * dilationFactor a m u * normalizedZeta F m u := by
  let r : ℂ := ‖(a : ℂ)‖
  let b (j : Fin (n + 1)) := direction (a : ℂ) ^ (-m j) * r ^ (-(2 * u j - 2))
  have hr : r ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero)
  have hp (j : Fin (n + 1)) (z : ℂ) :
      additiveWeight (m j) (u j) z = b j * additiveWeight (m j) (u j) ((a : ℂ) * z) := by
    rw [additiveWeight_mul]
    dsimp only [b]
    rw [zpow_neg, cpow_neg]
    have hd := zpow_ne_zero (m j) (direction_ne_zero a.ne_zero)
    have hq : r ^ (2 * u j - 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hr)
    change _ = ((direction (a : ℂ) ^ m j)⁻¹ * (r ^ (2 * u j - 2))⁻¹) *
      ((direction (a : ℂ) ^ m j * r ^ (2 * u j - 2)) * _)
    generalize direction (a : ℂ) ^ m j = d at hd ⊢
    generalize r ^ (2 * u j - 2) = q at hq ⊢
    field_simp
  have he (z : V) : integrand (k • dilate a F : 𝓢(V, ℂ)) m u z =
      (k * ∏ j, b j) * integrand F m u (vectorDilation a z) := by
    simp only [integrand, smul_apply, smul_eq_mul, dilate,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    nth_rw 1 [show (∏ j, additiveWeight (m j) (u j) (z j)) =
        ∏ j, b j * additiveWeight (m j) (u j) (vectorDilation a z j) from
      Finset.prod_congr rfl fun j _ => hp j (z j)]
    rw [Finset.prod_mul_distrib]
    ring
  have hδ : ((density a : ℝ) : ℂ) = r ^ (-(2 : ℂ)) := by
    rw [cpow_neg]
    simp only [density, NNReal.coe_inv, NNReal.coe_pow, coe_nnnorm, ofReal_inv, ofReal_pow]
    congr 1
    exact (Complex.cpow_ofNat r 2).symm
  have hB : (∏ j, b j) * ((density a : ℝ) : ℂ) ^ (n + 1) = dilationFactor a m u := by
    have hC : (∏ _ : Fin (n + 1), ((density a : ℝ) : ℂ)) = ((density a : ℝ) : ℂ) ^ (n + 1) := by
      simp
    rw [← hC, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [b]
    rw [hδ, mul_assoc, ← cpow_add _ _ hr, show -(2 * u j - 2) + -(2 : ℂ) = -2 * u j by ring]
  unfold normalizedZeta zeta
  simp only [he, integral_const_mul, integral_vectorDilation, Complex.real_smul, ofReal_pow]
  linear_combination
    ((∏ j, gammaNormalizer (m j) (u j)) * k * ∫ z, integrand F m u z) * hB

private theorem differentiable_dilationFactor (a : ℂˣ) (m : W) (t : V) (c : Fin (n + 1) → ℝ) :
    Differentiable ℂ (fun w => dilationFactor a m (affineParameter t c w)) := by
  change Differentiable ℂ (fun w => ∏ j, direction (a : ℂ) ^ (-m j) *
    (‖(a : ℂ)‖ : ℂ) ^ (-2 * affineParameter t c w j))
  apply Differentiable.fun_finsetProd
  intro j _
  have h : Differentiable ℂ (fun w => affineParameter t c w j) := by
    unfold affineParameter
    fun_prop
  exact (h.const_mul (-2)).const_cpow
    (Or.inl (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero))) |>.const_mul _

private theorem entire_dilate_smul
    {H : 𝓢(V, ℂ) → W → V → ℂ} (hH : IsEntireNormalization H)
    (a : ℂˣ) (k : ℂ) (F : 𝓢(V, ℂ)) (m : W) (u : V) :
    H (k • dilate a F) m u = k * dilationFactor a m u * H F m u := by
  let c (j : Fin (n + 1)) := 1 + |(u j).re|
  let U := affineParameter u c
  have h₁ (j : Fin (n + 1)) : 0 < (U 1 j).re := by
    simp only [U, affineParameter, mul_one, add_re, ofReal_re, c]
    linarith [neg_abs_le (u j).re]
  have hevent : ∀ᶠ w in 𝓝 (1 : ℂ), ∀ j, 0 < (U w j).re := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun w : ℂ => (U w j).re) :=
      continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id))
    exact (isOpen_lt continuous_const hc).mem_nhds (h₁ j)
  have ha : AnalyticOnNhd ℂ (fun w => H (k • dilate a F) m (U w)) univ :=
    fun w _ => (hH.1 _ m u c).analyticAt w
  have hb : AnalyticOnNhd ℂ (fun w => k * dilationFactor a m (U w) * H F m (U w)) univ :=
    fun w _ => (((differentiable_dilationFactor a m u c).const_mul k).mul (hH.1 F m u c)).analyticAt w
  have he : (fun w => H (k • dilate a F) m (U w)) =ᶠ[𝓝 (1 : ℂ)]
      fun w => k * dilationFactor a m (U w) * H F m (U w) := by
    filter_upwards [hevent] with w hw
    rw [hH.2 _ m _ hw, hH.2 F m _ hw, normalizedZeta_dilate_smul]
  have hzero : U 0 = u := by funext j; simp [U, affineParameter]
  have h := congrFun (ha.eq_of_eventuallyEq hb he) 0
  change H (k • dilate a F) m (U 0) = k * dilationFactor a m (U 0) * H F m (U 0) at h
  rwa [hzero] at h

private theorem transform_scale (a : ℂˣ) (F : 𝓢(V, ℂ)) :
    ComplexTraceFourier.transform a F =
      (‖(a : ℂ)‖ : ℂ) ^ (n + 1) • dilate (-a) (ComplexTraceFourier.transform (-1) F) := by
  let μ (a : ℂˣ) := Measure.pi (fun _ : Fin (n + 1) => (complexSelfDualMeasure a).measure)
  have hμ : μ a = ‖(a : ℂ)‖₊ ^ (n + 1) • μ (-1) := by
    unfold μ
    rw [ComplexTraceFourier.product_measure_eq, ComplexTraceFourier.product_measure_eq,
      Fintype.card_fin, smul_smul]
    simp [ComplexTraceFourier.scale, mul_pow, mul_comm]
  ext x
  change ComplexTraceFourier.transform a F x =
    ((‖(a : ℂ)‖ : ℂ) ^ (n + 1)) * ComplexTraceFourier.transform (-1) F (vectorDilation (-a) x)
  rw [ComplexTraceFourier.transform_apply a F x, ComplexTraceFourier.transform_apply (-1) F _]
  change (∫ y, _ ∂μ a) = _
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow, coe_nnnorm,
    Complex.real_smul, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
    vectorDilation_apply, Units.val_neg, Units.val_one, neg_mul, one_mul, neg_neg, mul_neg,
    Finset.sum_neg_distrib]
  congr 3
  rw [Finset.mul_sum]
  exact congrArg (fun z : ℂ => -z) (Finset.sum_congr rfl fun _ _ => by ring)

private theorem scalar_epsilon_formula (a : ℂˣ) (m : ℤ) (u : ℂ) :
    ((characterOfParams m 0).epsilon (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) u : ℂ) =
      (‖(a : ℂ)‖ : ℂ) *
        (direction (-(a : ℂ)) ^ (-(-m)) * (‖(-(a : ℂ))‖ : ℂ) ^ (-2 * (1 - u))) *
        I ^ m.natAbs := by
  rw [ComplexCharacterData.coe_epsilon, (characterOfParams m 0).character_eq]
  simp only [characterOfParams_weight, characterOfParams_exponent, mul_zero, cpow_zero, mul_one,
    Units.val_neg, norm_neg, direction, neg_neg, coe_nnnorm]
  rw [show 2 * (u - 1) = -2 * (1 - u) by ring]
  ring

/-- The entire product Tate identity for the negative trace Fourier transform at any nonzero
character parameter, with the chosen self-dual measure in every coordinate. -/
def ComplexTateProductScaledReflectionStatement : Prop :=
  ∀ (n : ℕ) (H : 𝓢(Fin (n + 1) → ℂ, ℂ) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℂ) → ℂ),
    IsEntireNormalization H → ∀ (a : ℂˣ) F m u,
      H (ComplexTraceFourier.transform a F) (fun j => -m j) (fun j => 1 - u j) =
        (∏ j, ((characterOfParams (m j) 0).epsilon (-a) ‖(a : ℂ)‖₊
          (nnnorm_pos.mpr a.ne_zero) (u j) : ℂ)) * H F m u

theorem complexTateProductScaledReflection : ComplexTateProductScaledReflectionStatement := by
  intro n H hH a F m u
  rw [transform_scale a F, entire_dilate_smul hH, complexTateProductEntireReflection n H hH,
    ← mul_assoc]
  congr 1
  have hc : (∏ _ : Fin (n + 1), (‖(a : ℂ)‖ : ℂ)) = (‖(a : ℂ)‖ : ℂ) ^ (n + 1) := by simp
  rw [← hc, dilationFactor, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simpa only [mul_assoc, Units.val_neg] using (scalar_epsilon_formula a (m j) (u j)).symm

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
