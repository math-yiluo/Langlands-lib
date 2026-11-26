import Langlands.Global.AdelicBiFiniteConvolutionApproximation
import Langlands.Global.AdelicTestConvolution

/-! # Approximate identities localized at the finite adelic places -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set
open scoped CategoryTheory.MonObj Pointwise Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "dg" => (Measure.haar : Measure A)

omit [LocallyOfFiniteType G.X.hom] in
/-- A kernel is supported over a finite adelic subgroup when its values vanish outside
the inverse image of the subgroup. -/
def HasFiniteProjectionSupport (L : Subgroup Af) (h : A → ℂ) : Prop :=
  ∀ x, h x ≠ 0 → finite F G x ∈ L

/-- Right convolution approximates a finite continuous family on a compact set, with
the approximating smooth kernels confined to any prescribed identity neighborhood. -/
theorem exists_rightConvolution_approximation_in_nhds {d m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : Fin m → C(A, ℂ))
    {V : Set A} (hV : V ∈ 𝓝 1) {C : Set A} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ (∀ x, h x ≠ 0 → x ∈ V) ∧
      ∀ i x, x ∈ C → ‖rightConvolution F G h (f i) x - f i x‖ ≤ ε := by
  let Near : Set A := {t | ∀ i, ∀ x ∈ C, ‖f i (x * t) - f i x‖ < ε}
  have hNear : Near ∈ 𝓝 1 := by
    change ∀ᶠ t in 𝓝 (1 : A), ∀ i, ∀ x ∈ C, ‖f i (x * t) - f i x‖ < ε
    rw [Filter.eventually_all]
    intro i
    apply hC.eventually_forall_of_forall_eventually
    intro x _
    have hc : Continuous (fun z : A × A => ‖f i (z.2 * z.1) - f i z.2‖) :=
      (((f i).continuous.comp (continuous_snd.mul continuous_fst)).sub
        ((f i).continuous.comp continuous_snd)).norm
    exact hc.continuousAt.eventually_lt (g := fun _ => ε) continuousAt_const (by simpa using hε)
  obtain ⟨k, hk, hsupp, hn, hm⟩ :=
    exists_normalizedAdelicTestFunction hsmooth (inter_mem hV hNear)
  let h (t : A) : ℂ := k t
  have hzero (t : A) (ht : t ∉ tsupport k) : h t = 0 := by
    simp only [h, image_eq_zero_of_notMem_tsupport ht, Complex.ofReal_zero]
  have hkernel (t : A) (ht : h t ≠ 0) : t ∈ tsupport k := by
    by_contra hnmem
    exact ht (hzero t hnmem)
  refine ⟨h, hk, fun t ht => (hsupp (hkernel t ht)).1, fun i x hx => ?_⟩
  have hi : Integrable (fun t => h t * f i (x * t)) dg :=
    (hk.1.1.mul ((f i).continuous.comp (continuous_const.mul continuous_id)))
      |>.integrable_of_hasCompactSupport hk.2.1.mul_right
  have hic : Integrable (fun t => h t * f i x) dg :=
    (hk.1.1.mul continuous_const).integrable_of_hasCompactSupport hk.2.1.mul_right
  have hkc : (∫ t, h t * f i x ∂dg) = f i x := by
    rw [integral_mul_const, show h = (fun t => (k t : ℂ)) from rfl,
      integral_complex_ofReal, hm, Complex.ofReal_one, one_mul]
  calc
    _ = ‖∫ t, h t * (f i (x * t) - f i x) ∂dg‖ := by
      simp only [mul_sub, integral_sub hi hic, hkc, rightConvolution]
    _ ≤ ∫ t, ε * k t ∂dg := by
      have hkint : Integrable (Complex.re ∘ h) dg :=
        (Complex.continuous_re.comp hk.1.1).integrable_of_hasCompactSupport
          (hk.2.1.comp_left Complex.zero_re)
      have hdom : Integrable (fun t => ε * k t) dg := by
        simpa only [Function.comp_apply, h, Complex.ofReal_re] using hkint.const_mul ε
      apply norm_integral_le_of_norm_le hdom
      apply Filter.Eventually.of_forall
      intro t
      by_cases ht : t ∈ tsupport k
      · simp only [norm_mul, h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hn t),
          mul_comm ε]
        exact mul_le_mul_of_nonneg_left ((hsupp ht).2 i x hx).le (hn t)
      · simp only [hzero t ht, zero_mul, norm_zero, image_eq_zero_of_notMem_tsupport ht, mul_zero, le_refl]
    _ = ε := by rw [integral_const_mul, hm, mul_one]

section CompactAverages

variable {K : Subgroup (InfiniteAdelicGroupPoints F G)} [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K] (measure : Measure K) [measure.IsHaarMeasure]

omit [LocallyOfFiniteType G.X.hom] [CompactSpace K] [BorelSpace K] [measure.IsHaarMeasure] in
/-- Infinite compact averages preserve support over a finite adelic subgroup. -/
theorem hasFiniteProjectionSupport_averaged {L : Subgroup Af} {h : A → ℂ}
    (hs : HasFiniteProjectionSupport L h) (a b : C(K, ℂ)) :
    HasFiniteProjectionSupport L
      (leftCompactKernelAverage measure a (rightCompactKernelAverage measure b h)) := by
  intro x hx
  by_contra hxL
  apply hx
  unfold leftCompactKernelAverage
  apply integral_eq_zero_of_ae
  filter_upwards with k
  apply mul_eq_zero.mpr
  right
  unfold rightCompactKernelAverage
  apply integral_eq_zero_of_ae
  filter_upwards with l
  apply mul_eq_zero.mpr
  right
  by_contra hne
  apply hxL
  have hval := hs ((ofInfinite F G k.val)⁻¹ * x * ofInfinite F G l.val) hne
  simpa only [map_mul, map_inv, finite_ofInfinite, inv_one, one_mul, mul_one] using hval

/-- Approximation by fixed compact averaging weights can be localized over any
open finite adelic subgroup. The weights must reproduce the supplied family. -/
theorem exists_averaged_rightConvolution_approximation_of_finite_support {d m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : Fin m → C(A, ℂ))
    (a b : C(K, ℂ))
    (hafix : ∀ i x, (∫ k, a k * f i (x * ofInfinite F G k.val) ∂measure) = f i x)
    (hbfix : ∀ i x, (∫ k, b k * f i (x * (ofInfinite F G k.val)⁻¹) ∂measure) = f i x)
    (L : Subgroup Af) (hL : IsOpen (L : Set Af)) {C : Set A} (hC : IsCompact C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ HasFiniteProjectionSupport L h ∧
      ∀ i x, x ∈ C →
        ‖rightConvolution F G (leftCompactKernelAverage measure a
          (rightCompactKernelAverage measure b h)) (f i) x - f i x‖ ≤ ε := by
  let inc (k : K) : A := ofInfinite F G k.val
  have hinc : Continuous inc := (ofInfinite F G).continuous.comp continuous_subtype_val
  have hV : (finite F G) ⁻¹' (L : Set Af) ∈ 𝓝 (1 : A) :=
    (hL.preimage (finite F G).continuous).mem_nhds (by simp)
  let M : ℝ := ∫ k, ‖a k‖ ∂measure
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨h, hh, hs, happrox⟩ := exists_rightConvolution_approximation_in_nhds hsmooth f hV
    (hC.mul (isCompact_range hinc)) hδ
  let r := rightCompactKernelAverage measure b h
  have hr := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  have hrconv (i : Fin m) (x : A) :
      rightConvolution F G r (f i) x = rightConvolution F G h (f i) x := by
    unfold r
    rw [rightConvolution_rightCompactKernelAverage measure b hh.1.1 hh.2.1 (f i).continuous]
    exact congrArg (fun v => rightConvolution F G h v x) (funext (hbfix i))
  refine ⟨h, hh, hs, fun i x hx => ?_⟩
  rw [rightConvolution_leftCompactKernelAverage measure a hr.1.1 hr.2.1 (f i).continuous]
  change ‖(∫ k, a k * rightConvolution F G r (f i) (x * inc k) ∂measure) - f i x‖ ≤ ε
  simp only [hrconv]
  let D (k : K) := rightConvolution F G h (f i) (x * inc k)
  let v (k : K) := f i (x * inc k)
  have hD : Continuous D := ((rightConvolutionEnd hsmooth hh) (f i)).continuous.comp
    (continuous_const.mul hinc)
  have hv : Continuous v := (f i).continuous.comp (continuous_const.mul hinc)
  have hint (w : K → ℂ) (hw : Continuous w) :
      Integrable (fun k => a k * w k) measure :=
    (a.continuous.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ‖(∫ k, a k * D k ∂measure) - f i x‖ ≤ ε
  rw [← hafix i x, ← integral_sub (hint D hD) (hint v hv)]
  calc
    _ ≤ ∫ k, δ * ‖a k‖ ∂measure := norm_integral_le_of_norm_le
      ((a.continuous.norm.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul δ)
      (Filter.Eventually.of_forall fun k => by
        rw [← mul_sub, norm_mul, mul_comm δ]
        exact mul_le_mul_of_nonneg_left
          (happrox i _ ⟨x, hx, inc k, ⟨k, rfl⟩, rfl⟩) (norm_nonneg _))
    _ = δ * M := integral_const_mul _ _
    _ ≤ δ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = ε := div_mul_cancel₀ _ (by positivity)

end CompactAverages

/-- Positive convolution powers keep the same finite adelic subgroup support. -/
theorem hasFiniteProjectionSupport_positiveConvolutionPower {L : Subgroup Af}
    {h : A → ℂ} (hs : HasFiniteProjectionSupport L h) (j : ℕ) :
    HasFiniteProjectionSupport L (positiveConvolutionPower h j) := by
  induction j with
  | zero => exact hs
  | succ j ih =>
    intro x hx
    by_contra hxL
    apply hx
    unfold positiveConvolutionPower Hecke.convolutionIntegral
    apply integral_eq_zero_of_ae
    filter_upwards with y
    by_contra hprod
    obtain ⟨hy, hyx⟩ := mul_ne_zero_iff.mp hprod
    apply hxL
    have hmem := L.mul_mem (hs y hy) (ih (y⁻¹ * x) hyx)
    simpa only [← map_mul, mul_inv_cancel_left] using hmem

end Langlands.Global.AdelicGroupPoints
