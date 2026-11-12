import Langlands.Representation.Hecke.CompactInductionStatements

/-! Compact-support change of variables and the right action of III.2.6. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure MulOpposite
open scoped Pointwise

namespace Langlands.Hecke

open HarmonicAnalysis

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Right translation of a test-function integral, with no countability or
regularity condition on the supplied Haar measure. -/
theorem integral_mul_right_test (f : SchwartzBruhat G) (g : G) :
    (∫ x, f (x * g) ∂μ) = haarScale g * ∫ x, f x ∂μ := by
  let ν : Measure G := μ.map (· * g)
  have hre : (∫ x, (f x).re ∂ν) =
      (modularCharacter g : ℝ) * ∫ x, (f x).re ∂μ := by
    rw [integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ
      (f := fun x => (f x).re) (Complex.continuous_re.comp f.continuous)
      (f.hasCompactSupport.comp_left (g := Complex.re) rfl),
      integral_smul_nnreal_measure]
    rw [← modularCharacterFun_eq_haarScalarFactor μ g]
    rfl
  have him : (∫ x, (f x).im ∂ν) =
      (modularCharacter g : ℝ) * ∫ x, (f x).im ∂μ := by
    rw [integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ
      (f := fun x => (f x).im) (Complex.continuous_im.comp f.continuous)
      (f.hasCompactSupport.comp_left (g := Complex.im) rfl),
      integral_smul_nnreal_measure]
    rw [← modularCharacterFun_eq_haarScalarFactor μ g]
    rfl
  have hreν : (∫ x, (f x).re ∂ν) = (∫ x, f x ∂ν).re := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.integral_comp_comm
        (f.continuous.integrable_of_hasCompactSupport (μ := ν) f.hasCompactSupport)
  have hreμ : (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.integral_comp_comm
        (f.continuous.integrable_of_hasCompactSupport (μ := μ) f.hasCompactSupport)
  have himν : (∫ x, (f x).im ∂ν) = (∫ x, f x ∂ν).im := by
    simpa only [Complex.imCLM_apply] using
      Complex.imCLM.integral_comp_comm
        (f.continuous.integrable_of_hasCompactSupport (μ := ν) f.hasCompactSupport)
  have himμ : (∫ x, (f x).im ∂μ) = (∫ x, f x ∂μ).im := by
    simpa only [Complex.imCLM_apply] using
      Complex.imCLM.integral_comp_comm
        (f.continuous.integrable_of_hasCompactSupport (μ := μ) f.hasCompactSupport)
  rw [← (measurableEmbedding_mulRight g).integral_map]
  change (∫ x, f x ∂ν) = _
  apply Complex.ext
  · rw [← hreν, hre, Complex.mul_re]
    simp [haarScale, hreμ]
  · rw [← himν, him, Complex.mul_im]
    simp [haarScale, himμ]

private theorem inversionKernel_compact (f e : SchwartzBruhat G) :
    HasCompactSupport (fun p : G × G => f p.1 * e (p.2 * p.1)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((TestFunction.isCompact_support f).prod
      ((TestFunction.isCompact_support e).mul (TestFunction.isCompact_support f).inv))
  rintro ⟨x, y⟩ hp
  have h := mul_ne_zero_iff.mp hp
  exact ⟨h.1, ⟨y * x, h.2, x⁻¹, by simpa using h.1, by simp⟩⟩

private theorem inversionKernel'_compact (f e : SchwartzBruhat G) :
    HasCompactSupport (fun p : G × G => f (p.1⁻¹ * p.2) * e p.2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (((TestFunction.isCompact_support e).mul (TestFunction.isCompact_support f).inv).prod
      (TestFunction.isCompact_support e))
  rintro ⟨y, z⟩ hp
  have h := mul_ne_zero_iff.mp hp
  refine ⟨⟨z, h.2, (y⁻¹ * z)⁻¹, by simpa using h.1, ?_⟩, h.2⟩
  simp

/-- The compact-support form of Haar inversion, using Fubini rather than any
regularity property of the supplied Haar measure. -/
theorem integral_inv_test (f : SchwartzBruhat G) :
    (∫ x, f x⁻¹ ∂μ) = ∫ x, f x * haarScale x ∂μ := by
  obtain ⟨K, hK, _, _, _⟩ := HeckeAlgebra.finiteFamilyLocalUnits G μ ∅ ⊤
  let e : SchwartzBruhat G := HeckeAlgebra.normalizedIndicator μ K hK
  have he : (∫ x, e x ∂μ) = 1 := by
    change (∫ x, (μ.real (K : Set G) : ℂ)⁻¹ *
      (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ) = 1
    rw [integral_const_mul, integral_indicator_const 1 K.isOpen.measurableSet]
    simpa only [Complex.real_smul, smul_eq_mul, mul_one] using
      inv_mul_cancel₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK)
  calc
    (∫ x, f x⁻¹ ∂μ) = (∫ x, f x⁻¹ ∂μ) * ∫ z, e z ∂μ := by rw [he, mul_one]
    _ = ∫ z, (∫ x, f x⁻¹ ∂μ) * e z ∂μ := (integral_const_mul _ _).symm
    _ = ∫ z, (∫ y, f (y⁻¹ * z) ∂μ) * e z ∂μ := by
      congr 1
      funext z
      congr 1
      simpa only [mul_inv_rev, inv_mul_cancel_right] using
        integral_mul_left_eq_self (μ := μ) (fun y => f (y⁻¹ * z)) z
    _ = ∫ z, ∫ y, f (y⁻¹ * z) * e z ∂μ ∂μ := by
      simp only [integral_mul_const]
    _ = ∫ y, ∫ z, f (y⁻¹ * z) * e z ∂μ ∂μ := by
      symm
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp (continuous_fst.inv.mul continuous_snd)).mul
          (e.continuous.comp continuous_snd)
      · exact inversionKernel'_compact f e
    _ = ∫ y, ∫ x, f x * e (y * x) ∂μ ∂μ := by
      congr 1
      funext y
      simpa only [inv_mul_cancel_left] using
        (integral_mul_left_eq_self (μ := μ) (fun x => f (y⁻¹ * x) * e x) y).symm
    _ = ∫ x, ∫ y, f x * e (y * x) ∂μ ∂μ := by
      symm
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp continuous_fst).mul
          (e.continuous.comp (continuous_snd.mul continuous_fst))
      · exact inversionKernel_compact f e
    _ = ∫ x, f x * (haarScale x * ∫ y, e y ∂μ) ∂μ := by
      simp only [integral_const_mul, integral_mul_right_test μ e]
    _ = _ := by simp only [he, mul_one]

/-- Weighted inversion preserves the integral of every actual Hecke test function. -/
theorem integral_haarInversion (f : HeckeAlgebra μ) :
    (∫ x, haarInversion μ f x ∂μ) = ∫ x, f x ∂μ := by
  let hf : SchwartzBruhat G :=
    ⟨fun x => f x⁻¹, f.locallyConstant.comp_continuous continuous_inv,
      f.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)⟩
  have h := integral_inv_test μ hf
  simpa only [hf, haarInversion_apply, inv_inv, mul_comm] using h.symm

namespace Homomorphism

variable {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- The compactly supported subgroup test function appearing in the right
convolution formula. -/
def rightConvolutionKernel (a : HeckeAlgebra μH) (f : HeckeAlgebra μ) (x : G) :
    SchwartzBruhat H :=
  ⟨fun h => haarScale (φ h) * a h * f (x * (φ h)⁻¹),
    ((haarScale_locallyConstant.comp_continuous hφ).mul a.locallyConstant).mul
      (f.locallyConstant.comp_continuous (continuous_const.mul hφ.inv)),
    a.hasCompactSupport.mul_left.mul_right⟩

/-- The original right module has the modularly weighted right-convolution
formula, for every continuous homomorphism. -/
theorem rightModule_integral (a : HeckeAlgebra μH) (f : HeckeAlgebra μ) (x : G) :
    (letI := rightModule μ μH φ hφ; (op a • f) x) =
      ∫ h, haarScale (φ h) * a h * f (x * (φ h)⁻¹) ∂μH := by
  let b := rightConvolutionKernel μ μH φ hφ a f x
  change haarScale x *
    (letI := leftModule μ μH φ hφ
     (haarInversion μH a • haarInversion μ f) x⁻¹) = _
  rw [leftModule_apply, ← integral_const_mul]
  calc
    _ = ∫ h, haarInversion μH b h ∂μH := by
      apply integral_congr_ae
      filter_upwards [] with h
      change haarScale x *
          (haarScale h * a h⁻¹ *
            (haarScale ((φ h)⁻¹ * x⁻¹) * f (((φ h)⁻¹ * x⁻¹)⁻¹))) =
        haarScale h * (haarScale (φ h⁻¹) * a h⁻¹ * f (x * (φ h⁻¹)⁻¹))
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      have hx : haarScale x * (haarScale x)⁻¹ = 1 := by
        simpa only [map_inv] using haarScale_mul_inverse x
      calc
        _ = (haarScale x * (haarScale x)⁻¹) *
            (haarScale h * a h⁻¹ * (haarScale (φ h))⁻¹ * f (x * φ h)) := by ring
        _ = _ := by rw [hx, one_mul]; ring
    _ = _ := integral_haarInversion μH b

end Homomorphism

end Langlands.Hecke
