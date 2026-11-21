import Langlands.Analysis.CompactManifoldVectorIntegral
import Langlands.Analysis.FixedSupportTestFamily
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Differentiating functionals of joint smooth test families -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology Manifold

namespace Langlands.Analysis

universe u

private theorem contDiff_integral_unitInterval {A : Type u} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] {H : A × ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, H (x, t)) := by
  let J := Icc (0 : ℝ) 1
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  let μJ := (volume : Measure ℝ).comap (Subtype.val : J → ℝ)
  let : IsFiniteMeasure μJ := ⟨by
    have e := MeasurableEmbedding.subtype_coe (s := J) measurableSet_Icc
    change ((volume : Measure ℝ).comap (Subtype.val : J → ℝ)) univ < ⊤
    rw [e.comap_apply, image_univ, Subtype.range_coe_subtype]
    exact isCompact_Icc.measure_lt_top⟩
  let j : C(J, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hH' : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ H := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hH.contMDiff
  apply contDiffOn_univ.mp
  refine (CompactManifoldVectorIntegral.contDiffOn_weightedIntegral μJ (1 : C(J, ℂ)) j
    isOpen_univ hH'.contMDiffOn).congr ?_
  intro x _
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  simp only [ContinuousMap.one_apply, one_smul]
  exact (integral_subtype_comap measurableSet_Icc (fun t => H (x, t))).symm

variable {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

/-- Applying a continuous real linear functional to a jointly smooth
test family differentiates the test in the parameter, provided the
family and its derivative have the indicated common compact support. -/
theorem hasDerivAt_fixedSupportTestFamily {K : Compacts A} {s : Set ℝ} (hs : IsOpen s)
    (h0 : (0 : ℝ) ∈ s) {H : ℝ × A → ℂ} (hH : ContDiff ℝ ∞ H)
    (f : ℝ → 𝓓_{K}(A, ℂ)) (hf : ∀ t ∈ s, ∀ x : A, f t x = H (t, x))
    (g : 𝓓_{K}(A, ℂ)) (hg : ∀ x : A, g x = fderiv ℝ H (0, x) (1, 0))
    (T : 𝓓_{K}(A, ℂ) →L[ℝ] ℂ) :
    HasDerivAt (fun t => T (f t)) (T g) 0 := by
  classical
  let W (p : (ℝ × A) × ℝ) : ℂ := fderiv ℝ H (p.2 * p.1.1, p.1.2) (1, 0)
  have hW : ContDiff ℝ ∞ W :=
    ((hH.fderiv_right (m := ∞) (by simp)).comp
      ((contDiff_snd.mul contDiff_fst.fst).prodMk contDiff_fst.snd)).clm_apply contDiff_const
  let R (p : ℝ × A) := ∫ q in (0 : ℝ)..1, W (p, q)
  have hR : ContDiff ℝ ∞ R := contDiff_integral_unitInterval hW
  have hR₀ (x : A) : R (0, x) = g x := by
    change (∫ q in (0 : ℝ)..1, fderiv ℝ H (q * 0, x) (1, 0)) = g x
    rw [hg]
    simp only [mul_zero, intervalIntegral.integral_const, sub_zero, one_smul]
  have hR_eq (t : ℝ) (x : A) : t • R (t, x) = H (t, x) - H (0, x) := by
    have h (q : ℝ) : HasDerivAt (fun v : ℝ => H (v * t, x)) (t • W ((t, x), q)) q := by
      have hd : DifferentiableAt ℝ H (q * t, x) := hH.contDiffAt.differentiableAt (by simp)
      have hpath : HasDerivAt (fun v : ℝ => (v * t, x)) (t, 0) q := by
        simpa only [id_eq, one_mul] using
          (((hasDerivAt_id q).mul_const t).prodMk (hasDerivAt_const q x))
      have hd' := hd.hasFDerivAt.comp_hasDerivAt q hpath
      have he : t • W ((t, x), q) = fderiv ℝ H (q * t, x) (t, 0) := by
        change t • fderiv ℝ H (q * t, x) (1, 0) = _
        rw [← map_smul]
        congr 1
        change (t * 1, t • (0 : A)) = (t, 0)
        rw [mul_one, smul_zero]
      rw [he]
      exact hd'
    have hcont : Continuous (fun q : ℝ => t • W ((t, x), q)) :=
      (hW.continuous.comp (continuous_const.prodMk continuous_id)).const_smul t
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := 1) (fun q _ => h q) (hcont.intervalIntegrable 0 1)
    simpa only [R, intervalIntegral.integral_smul, one_mul, zero_mul] using hFTC
  have hzero (t : ℝ) (ht : t ∈ s) (x : A) (hx : x ∉ (K : Set A)) : R (t, x) = 0 := by
    by_cases ht₀ : t = 0
    · subst t
      exact (hR₀ x).trans (g.zero_on_compl hx)
    · have hu : H (t, x) = 0 := (hf t ht x).symm.trans ((f t).zero_on_compl hx)
      have hv : H (0, x) = 0 := (hf 0 h0 x).symm.trans ((f 0).zero_on_compl hx)
      have he : t • R (t, x) = 0 := by rw [hR_eq, hu, hv, sub_zero]
      exact (smul_eq_zero.mp he).resolve_left ht₀
  let Q (t : ℝ) : 𝓓_{K}(A, ℂ) :=
    if ht : t ∈ s then
      ⟨fun x => R (t, x), hR.comp (contDiff_const.prodMk contDiff_id), hzero t ht⟩
    else 0
  have hQ (t : ℝ) (ht : t ∈ s) (x : A) : Q t x = R (t, x) := by
    simp [Q, ht]
    rfl
  have hQg : Q 0 = g := by
    ext x
    exact (hQ 0 h0 x).trans (hR₀ x)
  have hQc : ContinuousAt Q 0 :=
    ((continuousOn_fixedSupportTestFamily hR Q hQ) 0 h0).continuousAt (hs.mem_nhds h0)
  have hlim : Tendsto (fun t => T (Q t)) (𝓝[≠] 0) (𝓝 (T g)) := by
    rw [← hQg]
    exact ((T.continuous.tendsto (Q 0)).comp hQc).mono_left nhdsWithin_le_nhds
  rw [hasDerivAt_iff_tendsto_slope]
  refine hlim.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hs.mem_nhds h0), self_mem_nhdsWithin] with t ht hne
  have ht₀ : t ≠ 0 := hne
  have hdiff : t • Q t = f t - f 0 := by
    ext x
    change t • Q t x = f t x - f 0 x
    rw [hQ t ht, hf t ht, hf 0 h0, hR_eq]
  rw [slope, vsub_eq_sub, sub_zero, ← map_sub, ← map_smul, ← hdiff, smul_smul,
    inv_mul_cancel₀ ht₀, one_smul]

end Langlands.Analysis
