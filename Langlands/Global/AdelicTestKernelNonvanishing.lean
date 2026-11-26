import Langlands.Global.AdelicRightConvolutionDifferentiation
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Compact smooth adelic kernels detect a nonzero value -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set Topology
open scoped CategoryTheory.MonObj Classical Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G

/-- Every identity neighborhood admits a real nonnegative smooth adelic test
kernel positive at the identity and supported inside the neighborhood. -/
theorem exists_nonnegativeTestKernel {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (U : Set A) (hU : U ∈ 𝓝 (1 : A)) :
    ∃ h : A → ℝ, IsAdelicTestFunction F G (fun x => (h x : ℂ)) ∧
      tsupport h ⊆ U ∧ (∀ x, 0 ≤ h x) ∧ 0 < h 1 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  have hU' : (split F G).symm ⁻¹' U ∈ 𝓝 ((1 : A∞), (1 : A_f)) := by
    apply (split F G).symm.continuous.continuousAt.preimage_mem_nhds
    change U ∈ 𝓝 ((split F G).symm 1)
    rwa [map_one]
  obtain ⟨V, W, hVo, hV₁, hWo, hW₁, hVW⟩ := mem_nhds_prod_iff'.mp hU'
  obtain ⟨K, hK, h₁, hKV⟩ := exists_compact_subset hVo hV₁
  obtain ⟨g, hgs, hgDiff, hgPos⟩ := isOpen_interior.exists_contMDiff_support_eq
    (n := (⊤ : ℕ∞)) (𝓘(ℝ, smoothModel F d)) (s := interior K)
  obtain ⟨L, hLc, hLW⟩ := ((finiteAdelicGroupCompactOpenBasis F G).2.mem_iff).mp (hWo.mem_nhds hW₁)
  let c : A_f → ℝ := (L : Set A_f).indicator fun _ => 1
  have hc : Continuous c := L.isClopen.continuous_indicator continuous_const
  have hc₀ (b : A_f) : 0 ≤ c b := indicator_nonneg (fun _ _ => zero_le_one) b
  have hcR (l : A_f) (hl : l ∈ L) (x : A_f) : c (x * l) = c x := by
    have he : x * l ∈ L ↔ x ∈ L := L.toSubgroup.mul_mem_cancel_right hl
    simp [c, indicator_apply, he]
  have hcL (l : A_f) (hl : l ∈ L) (x : A_f) : c (l * x) = c x := by
    have he : l * x ∈ L ↔ x ∈ L := L.toSubgroup.mul_mem_cancel_left hl
    simp [c, indicator_apply, he]
  let h (x : A) := g (infinite F G x) * c (finite F G x)
  have hhC : Continuous h :=
    (hgDiff.continuous.comp (infinite F G).continuous).mul (hc.comp (finite F G).continuous)
  have hh₀ (x : A) : 0 ≤ h x := mul_nonneg (hgPos _) (hc₀ _)
  have hSupport : tsupport h ⊆ (split F G).symm '' (K ×ˢ (L : Set A_f)) := by
    apply closure_minimal _ ((hK.prod hLc).image (split F G).symm.continuous).isClosed
    intro x hx
    refine ⟨(infinite F G x, finite F G x), ⟨?_, ?_⟩, (split F G).symm_apply_apply x⟩
    · apply interior_subset
      rw [← hgs]
      exact fun hg₀ => hx (by simp [h, hg₀])
    · by_contra hx'
      exact hx (by simp [h, c, indicator_of_notMem hx'])
  have hhS : HasCompactSupport h :=
    ((hK.prod hLc).image (split F G).symm.continuous).of_isClosed_subset
      (isClosed_tsupport h) hSupport
  refine ⟨h, ⟨⟨Complex.continuous_ofReal.comp hhC, ?_, L.toSubgroup, L.isOpen, ?_⟩,
    ?_, L.toSubgroup, L.isOpen, ?_⟩, ?_, hh₀, ?_⟩
  · intro b
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    change ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => (h (pair F G a b) : ℂ))
    simp only [h, infinite_pair, finite_pair]
    exact Complex.ofRealCLM.contDiff.contMDiff.comp (hgDiff.mul contMDiff_const)
  · intro l hl x
    change (h (x * ofFinite F G l) : ℂ) = (h x : ℂ)
    simp only [h, map_mul, infinite_ofFinite, mul_one, finite_ofFinite, hcR l hl]
  · exact hhS.comp_left Complex.ofReal_zero
  · intro l hl x
    change (h (ofFinite F G l * x) : ℂ) = (h x : ℂ)
    simp only [h, map_mul, infinite_ofFinite, one_mul, finite_ofFinite, hcL l hl]
  · exact hSupport.trans (by rintro _ ⟨y, hy, rfl⟩; exact hVW ⟨hKV hy.1, hLW hy.2⟩)
  · have hg₁ : g 1 ≠ 0 := by rw [← hgs] at h₁; exact h₁
    simpa [h, c, L.one_mem] using lt_of_le_of_ne (hgPos 1) hg₁.symm

/-- A continuous function nonzero at the identity has a compact smooth right
convolution that is nonzero at the identity. -/
def AdelicTestKernelNonvanishingStatement : Prop :=
  ∀ {d : ℕ}, SmoothOfRelativeDimension d G.X.hom →
  ∀ f : A → ℂ, Continuous f → f 1 ≠ 0 →
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ rightConvolution F G h f 1 ≠ 0

theorem adelicTestKernelNonvanishing : AdelicTestKernelNonvanishingStatement (F := F) (G := G) := by
  intro d hsmooth f hf hf₁
  let U : Set A := {x | 0 < (starRingEnd ℂ (f 1) * f x).re}
  have hp : (starRingEnd ℂ (f 1) * f 1).re = Complex.normSq (f 1) := by
    rw [mul_comm, Complex.mul_conj]
    simp
  have h₁ : 1 ∈ U := by
    change 0 < (starRingEnd ℂ (f 1) * f 1).re
    rw [hp]
    exact Complex.normSq_pos.mpr hf₁
  have hU : IsOpen U := isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_const.mul hf))
  obtain ⟨h, hh, hSupp, hh₀, hh₁⟩ := exists_nonnegativeTestKernel hsmooth U (hU.mem_nhds h₁)
  let w (a : A) : ℂ := (h a : ℂ) * (starRingEnd ℂ (f 1) * f a)
  have hw : Continuous w := hh.1.1.mul (continuous_const.mul hf)
  have hwS : HasCompactSupport w := hh.2.1.mul_right
  have hwRe (a : A) : (w a).re = h a * (starRingEnd ℂ (f 1) * f a).re := by
    simp [w, Complex.mul_re]
  have hw₀ : 0 ≤ fun a => (w a).re := by
    intro a
    change 0 ≤ (w a).re
    rw [hwRe]
    by_cases ha : a ∈ tsupport h
    · exact mul_nonneg (hh₀ a) (le_of_lt (hSupp ha))
    · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul]
  have hw₁ : 0 < (w 1).re := by rw [hwRe]; exact mul_pos hh₁ h₁
  refine ⟨fun x => (h x : ℂ), hh, ?_⟩
  have hInt : 0 < (∫ a, w a ∂(Measure.haar : Measure A)).re := by
    change 0 < RCLike.re (∫ a, w a ∂(Measure.haar : Measure A))
    rw [← integral_re (hw.integrable_of_hasCompactSupport hwS)]
    exact (Complex.continuous_re.comp hw).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hwS.comp_left Complex.zero_re) hw₀ hw₁.ne'
  have he : (∫ a, w a ∂(Measure.haar : Measure A)) =
      starRingEnd ℂ (f 1) * rightConvolution F G (fun x => (h x : ℂ)) f 1 := by
    rw [rightConvolution, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a => by simp only [one_mul, w]; ring
  intro h0
  rw [he, h0, mul_zero, Complex.zero_re] at hInt
  exact (lt_irrefl 0) hInt

end Langlands.Global.AdelicGroupPoints
