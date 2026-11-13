import Langlands.Representation.Hecke.OpenSubgroupInclusionStatement
import Langlands.HarmonicAnalysis.Distribution.Subspace

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.Hecke.Homomorphism

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsOpen (H : Set G)) [LocallyCompactSpace H]

include hH in
/-- On an open subgroup the ambient and subgroup modular characters agree. -/
theorem modularCharacter_subtype (h : H) :
    modularCharacter (h : G) = modularCharacter h := by
  let μ : Measure G := haar
  let ν : Measure H := μ.comap H.subtype
  let : ν.IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) μ hH.isOpenEmbedding_subtypeVal
  let : ν.Regular := Regular.comap' μ hH.isOpenEmbedding_subtypeVal
  obtain ⟨K, hK, hKH⟩ := Langlands.compactOpenSubgroupBasis G H (hH.mem_nhds H.one_mem)
  let S : Set H := H.subtype ⁻¹' (K : Set G)
  have himage : H.subtype '' S = (K : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hKH hx⟩, hx, rfl⟩
  have hpre :
      H.subtype '' ((fun y : H => y * h) ⁻¹' S) =
        (fun y : G => y * (h : G)) ⁻¹' (K : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hxH : x ∈ H := by
        have := H.mul_mem (hKH hx) (H.inv_mem h.property)
        simpa using this
      exact ⟨⟨x, hxH⟩, hx, rfl⟩
  have hmapG : map (· * (h : G)) μ = modularCharacterFun (h : G) • μ := by
    let : (map (· * (h : G)) μ).Regular := Regular.map (Homeomorph.mulRight (h : G))
    rw [modularCharacterFun_eq_haarScalarFactor μ]
    exact isMulLeftInvariant_eq_smul_of_regular _ μ
  have hG := congrArg (fun m : Measure G => m (K : Set G)) hmapG
  have hS : MeasurableSet S :=
    K.isOpen.measurableSet.preimage continuous_subtype_val.measurable
  have hmapH : map (· * h) ν = modularCharacterFun h • ν := by
    let : (map (· * h) ν).Regular := Regular.map (Homeomorph.mulRight h)
    rw [modularCharacterFun_eq_haarScalarFactor ν]
    exact isMulLeftInvariant_eq_smul_of_regular _ ν
  have hsub := congrArg (fun m : Measure H => m S) hmapH
  rw [map_apply (measurable_mul_const _) K.isOpen.measurableSet,
    Measure.smul_apply, nnreal_smul_coe_apply] at hG
  rw [map_apply (measurable_mul_const _) hS,
    Measure.smul_apply, nnreal_smul_coe_apply] at hsub
  have hν (A : Set H) : ν A = μ (H.subtype '' A) :=
    hH.isOpenEmbedding_subtypeVal.measurableEmbedding.comap_apply μ A
  rw [hν, hpre, hν, himage] at hsub
  have hpos : μ (K : Set G) ≠ 0 :=
    K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hfin : μ (K : Set G) ≠ ∞ := hK.measure_ne_top
  exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp (hG.symm.trans hsub)

include hH in
theorem haarScale_subtype (h : H) : haarScale (h : G) = haarScale h := by
  simp only [haarScale, MonoidHom.coe_mk, OneHom.coe_mk,
    modularCharacter_subtype H hH h]

include hH in
theorem open_relativeModularCharacter (h : H) :
    ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h : ℂ) = 1 := by
  change haarScale h * haarScale ((h⁻¹ : H) : G) = 1
  rw [haarScale_subtype H hH]
  exact haarScale_mul_inverse h

include hH in
theorem open_relativeModular (h : H) :
    HarmonicAnalysis.HomogeneousFunctions.relativeModular H
      (Subgroup.isClosed_of_isOpen H hH) h = 1 := by
  change modularCharacter ((h : G)⁻¹) / modularCharacter h⁻¹ = 1
  rw [show (h : G)⁻¹ = ((h⁻¹ : H) : G) from rfl,
    modularCharacter_subtype H hH]
  exact div_self (modularCharacterFun_pos h⁻¹).ne'

/-- Compactly supported complex integrals have the same Haar normalization law
as their real and imaginary parts, without regularity assumptions. -/
theorem integral_haar_complex (μ' μ : Measure G) [μ'.IsHaarMeasure] [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ x, f x ∂μ') = ((haarScalarFactor μ' μ : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  have hi' : Integrable f μ' := hf.integrable_of_hasCompactSupport hc
  have hi : Integrable f (haarScalarFactor μ' μ • μ) :=
    hf.integrable_of_hasCompactSupport hc
  have he : (∫ x, f x ∂μ') = ∫ x, f x ∂(haarScalarFactor μ' μ • μ) := by
    apply Complex.ext
    · calc
        _ = ∫ x, (f x).re ∂μ' := (integral_re hi').symm
        _ = ∫ x, (f x).re ∂(haarScalarFactor μ' μ • μ) :=
          integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ
            (Complex.continuous_re.comp hf) (hc.comp_left Complex.zero_re)
        _ = _ := integral_re hi
    · calc
        _ = ∫ x, (f x).im ∂μ' := (integral_im hi').symm
        _ = ∫ x, (f x).im ∂(haarScalarFactor μ' μ • μ) :=
          integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport μ' μ
            (Complex.continuous_im.comp hf) (hc.comp_left Complex.zero_im)
        _ = _ := integral_im hi
  rw [he, integral_smul_nnreal_measure]
  rfl

variable (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]

/-- The scalar converting a density for subgroup Haar into an ambient density. -/
def openDensity : ℂ := by
  let : (μG.comap H.subtype).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) μG hH.isOpenEmbedding_subtypeVal
  exact ((haarScalarFactor μH (μG.comap H.subtype) : ℝ) : ℂ)

/-- Zero extension with the density correction for the two supplied Haar measures. -/
def openHeckeLinear : HeckeAlgebra μH →ₗ[ℂ] HeckeAlgebra μG :=
  openDensity H hH μG μH •
    HarmonicAnalysis.SchwartzBruhat.extendZero hH

@[simp] theorem openHeckeLinear_apply_subtype (a : HeckeAlgebra μH) (h : H) :
    openHeckeLinear H hH μG μH a (h : G) =
      openDensity H hH μG μH * a h := by
  change _ * HarmonicAnalysis.SchwartzBruhat.extendZero hH a (h : G) = _
  exact congrArg (openDensity H hH μG μH * ·)
    (HarmonicAnalysis.SchwartzBruhat.extendZero_apply_subtype hH a h)

@[simp] theorem openHeckeLinear_apply_not_mem (a : HeckeAlgebra μH)
    {x : G} (hx : x ∉ H) : openHeckeLinear H hH μG μH a x = 0 := by
  change openDensity H hH μG μH *
    HarmonicAnalysis.SchwartzBruhat.extendZero hH a x = 0
  exact (congrArg (openDensity H hH μG μH * ·)
    (HarmonicAnalysis.SchwartzBruhat.extendZero_apply_of_not_mem hH a hx)).trans (mul_zero _)

theorem zeroExtension_mul_apply (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) (x : G) :
    ((show HeckeAlgebra μG from
      HarmonicAnalysis.SchwartzBruhat.extendZero hH a) * T) x =
      ∫ h : H, a h * T ((h : G)⁻¹ * x) ∂(μG.comap H.subtype) := by
  let E := HarmonicAnalysis.SchwartzBruhat.extendZero hH a
  change (∫ y, E y * T (y⁻¹ * x) ∂μG) = _
  calc
    _ = ∫ y in (H : Set G), E y * T (y⁻¹ * x) ∂μG := by
      rw [← integral_indicator hH.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ H
      · simp [hy]
      · simp [E, hy, HarmonicAnalysis.SchwartzBruhat.extendZero_apply_of_not_mem hH a hy]
    _ = _ := by
      rw [← integral_subtype_comap hH.measurableSet]
      change (∫ h : H, E (h : G) * T ((h : G)⁻¹ * x) ∂(μG.comap H.subtype)) = _
      apply integral_congr_ae
      filter_upwards [] with h
      exact congrArg (· * T ((h : G)⁻¹ * x))
        (HarmonicAnalysis.SchwartzBruhat.extendZero_apply_subtype hH a h)

theorem open_leftModule_eq (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) :
    (letI := leftModule μG μH H.subtype continuous_subtype_val; a • T) =
      openHeckeLinear H hH μG μH a * T := by
  let ν : Measure H := μG.comap H.subtype
  let : ν.IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) μG hH.isOpenEmbedding_subtypeVal
  apply TestFunction.ext
  intro x
  calc
    _ = ∫ h : H, a h * T ((h : G)⁻¹ * x) ∂μH :=
      leftModule_apply μG μH H.subtype continuous_subtype_val a T x
    _ = openDensity H hH μG μH *
        ∫ h : H, a h * T ((h : G)⁻¹ * x) ∂ν :=
      integral_haar_complex μH ν
        (a.continuous.mul (T.continuous.comp
          (continuous_subtype_val.inv.mul continuous_const))) a.hasCompactSupport.mul_right
    _ = _ := by
      change _ = ∫ y, (openDensity H hH μG μH *
        HarmonicAnalysis.SchwartzBruhat.extendZero hH a y) * T (y⁻¹ * x) ∂μG
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      exact congrArg (openDensity H hH μG μH * ·)
        (zeroExtension_mul_apply H hH μG μH a T x).symm

theorem openDensity_ne_zero : openDensity H hH μG μH ≠ 0 := by
  let : (μG.comap H.subtype).IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) μG hH.isOpenEmbedding_subtypeVal
  change ((haarScalarFactor μH (μG.comap H.subtype) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (haarScalarFactor_pos_of_isHaarMeasure μH (μG.comap H.subtype)).ne'

theorem openHeckeLinear_mul (a b : HeckeAlgebra μH) :
    openHeckeLinear H hH μG μH (a * b) =
      openHeckeLinear H hH μG μH a * openHeckeLinear H hH μG μH b := by
  letI := leftModule μG μH H.subtype continuous_subtype_val
  rw [← open_leftModule_eq H hH μG μH]
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ H
  · let h : H := ⟨x, hx⟩
    change openHeckeLinear H hH μG μH (a * b) (h : G) =
      (a • openHeckeLinear H hH μG μH b) (h : G)
    rw [openHeckeLinear_apply_subtype]
    calc
      _ = ∫ k : H, a k * (openDensity H hH μG μH * b (k⁻¹ * h)) ∂μH := by
        change _ * (∫ k : H, a k * b (k⁻¹ * h) ∂μH) = _
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with k
        ring
      _ = ∫ k : H, a k * openHeckeLinear H hH μG μH b
          ((k : G)⁻¹ * (h : G)) ∂μH := by
        apply integral_congr_ae
        filter_upwards [] with k
        exact congrArg (a k * ·) (openHeckeLinear_apply_subtype H hH μG μH b (k⁻¹ * h)).symm
      _ = _ := (leftModule_apply μG μH H.subtype continuous_subtype_val a _ _).symm
  · rw [openHeckeLinear_apply_not_mem H hH μG μH _ hx]
    symm
    calc
      _ = ∫ k : H, a k * openHeckeLinear H hH μG μH b ((k : G)⁻¹ * x) ∂μH :=
        leftModule_apply μG μH H.subtype continuous_subtype_val a _ _
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with k
        have hn : (k : G)⁻¹ * x ∉ H := by
          intro hk
          exact hx (by simpa using H.mul_mem k.property hk)
        rw [openHeckeLinear_apply_not_mem H hH μG μH _ hn, mul_zero]
        rfl

/-- The inclusion of Hecke densities for arbitrary choices of Haar measure. -/
def openHeckeInclusion : HeckeAlgebra μH →ₙ+* HeckeAlgebra μG where
  toFun := openHeckeLinear H hH μG μH
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := openHeckeLinear_mul H hH μG μH

theorem openHeckeLinear_surj_supported (T : HeckeAlgebra μG)
    (hT : ∀ x : G, x ∉ H → T x = 0) :
    ∃ a : HeckeAlgebra μH, openHeckeLinear H hH μG μH a = T := by
  let a : HeckeAlgebra μH := (openDensity H hH μG μH)⁻¹ •
    HarmonicAnalysis.SchwartzBruhat.restrictClosed (Subgroup.isClosed_of_isOpen H hH) T
  refine ⟨a, ?_⟩
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ H
  · let h : H := ⟨x, hx⟩
    change openHeckeLinear H hH μG μH a (h : G) = T (h : G)
    rw [openHeckeLinear_apply_subtype]
    change openDensity H hH μG μH * ((openDensity H hH μG μH)⁻¹ * T (h : G)) = _
    rw [← mul_assoc, mul_inv_cancel₀ (openDensity_ne_zero H hH μG μH), one_mul]
  · rw [openHeckeLinear_apply_not_mem H hH μG μH _ hx, hT x hx]

theorem openHeckeLinear_inversion (a : HeckeAlgebra μH) :
    haarInversion μG (openHeckeLinear H hH μG μH a) =
      openHeckeLinear H hH μG μH (haarInversion μH a) := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ H
  · let h : H := ⟨x, hx⟩
    change haarScale (h : G) * openHeckeLinear H hH μG μH a ((h⁻¹ : H) : G) =
      openHeckeLinear H hH μG μH (haarInversion μH a) (h : G)
    rw [openHeckeLinear_apply_subtype, openHeckeLinear_apply_subtype,
      haarScale_subtype H hH]
    change _ * (_ * _) = _ * (_ * _)
    ring
  · have hxi : x⁻¹ ∉ H := fun hi => hx (H.inv_mem_iff.mp hi)
    change haarScale x * openHeckeLinear H hH μG μH a x⁻¹ =
      openHeckeLinear H hH μG μH (haarInversion μH a) x
    rw [openHeckeLinear_apply_not_mem H hH μG μH _ hx,
      openHeckeLinear_apply_not_mem H hH μG μH _ hxi, mul_zero]

theorem open_rightModule_eq (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) :
    (letI := rightModule μG μH H.subtype continuous_subtype_val; MulOpposite.op a • T) =
      T * openHeckeLinear H hH μG μH a := by
  rw [rightModule_apply μG μH H.subtype continuous_subtype_val, open_leftModule_eq H hH μG μH,
    ← openHeckeLinear_inversion H hH μG μH, haarInversion_mul,
    haarInversion_involution, haarInversion_involution]

theorem openDensity_eq_one
    (hμ : ∀ s : Set H, μH s = μG (Subtype.val '' s)) :
    openDensity H hH μG μH = 1 := by
  have he : μG.comap H.subtype = μH := by
    ext s hs
    exact (hH.isOpenEmbedding_subtypeVal.measurableEmbedding.comap_apply μG s).trans (hμ s).symm
  simp only [openDensity, he, haarScalarFactor_self, NNReal.coe_one, Complex.ofReal_one]

end Langlands.Hecke.Homomorphism
