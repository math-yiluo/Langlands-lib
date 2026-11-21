import Langlands.Global.RankinSelberg.ArchimedeanTateTheta
import Langlands.Global.RankinSelberg.ArchimedeanMellinConvolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Real torus theta identity at determinant scale

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Real

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanDeterminantTheta

open ArchimedeanMellinPair ArchimedeanMellinConvolution ArchimedeanTateTheta
open Langlands.LocalFactor.RealTate

/-- The positive representative of the absolute product, equal to `|∏ xᵢ|` away from
coordinate hyperplanes. -/
def detScale {n : ℕ} (x : Fin n → ℝ) : ℝ := ∏ i, absPos (x i)

theorem detScale_pos {n : ℕ} (x : Fin n → ℝ) : 0 < detScale x :=
  Finset.prod_pos fun _ _ => absPos_pos _

theorem measurable_detScale {n : ℕ} : Measurable (detScale (n := n)) :=
  Finset.measurable_prod _ fun i _ => measurable_absPos.comp (measurable_pi_apply i)

/-- The density for the product of the characters `sgn^eᵢ |·|^uᵢ` and multiplicative measures,
multiplied by the test function `F`. -/
def weightedKernel {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (F : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  F x * ∏ i, integrand (fun _ => 1) (e i) (u i) (x i)

theorem aestronglyMeasurable_weightedKernel {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ)
    {F : (Fin n → ℝ) → ℂ} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (weightedKernel e u F) volume :=
  hF.mul (Finset.measurable_prod _ fun i _ =>
    (measurable_integrand measurable_const (e i) (u i)).comp (measurable_pi_apply i)).aestronglyMeasurable

theorem weightedKernel_mul_prod {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (F : (Fin n → ℝ) → ℂ) (h : Fin n → ℝ → ℂ) (a x : Fin n → ℝ) :
    weightedKernel e u F x * ∏ i, h i (a i * absPos (x i)) =
      F x * ∏ i, integrand (fun t => h i (a i * absPos t)) (e i) (u i) (x i) := by
  rw [weightedKernel, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    simpa only [one_mul] using integrand_mul_pair (fun _ => 1) (fun t => h i (a i * absPos t))
      (e i) (u i) (x i)

theorem continuous_fourierInvN {n : ℕ} {F : (Fin n → ℝ) → ℂ} (hF : Integrable F) :
    Continuous (fourierInvN F) := by
  refine continuous_of_dominated (bound := fun x => ‖F x‖) (fun y => ?_) (fun y => ?_)
    hF.norm ?_
  · have : Continuous (fun x : Fin n → ℝ =>
        Complex.exp (2 * (π : ℂ) * I * ((∑ i, x i * y i : ℝ) : ℂ))) := by fun_prop
    exact this.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact ae_of_all _ fun x => by rw [norm_mul, norm_exp_two_pi_I_mul', one_mul]
  · exact ae_of_all _ fun x => by fun_prop

/-- The first function of the determinant-scale Mellin pair. -/
def detH {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) : ℝ → ℂ :=
  mconv 1 (pairH (e 0) (u 0)) (fun j => pairH (e j.succ) (u j.succ))

/-- The second function of the determinant-scale Mellin pair. -/
def detK {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) : ℝ → ℂ :=
  mconv 1 (pairK (e 0) (u 0)) (fun j => pairK (e j.succ) (u j.succ))

theorem measurable_detH {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) :
    Measurable (detH e u) := measurable_mconv 1 (measurable_pairH _ _) (fun _ => measurable_pairH _ _)

theorem measurable_detK {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) :
    Measurable (detK e u) := measurable_mconv 1 (measurable_pairK _ _) (fun _ => measurable_pairK _ _)

theorem rapidDecay_detH {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) :
    RapidDecay (detH e u) := rapidDecay_mconv one_ne_zero (rapidDecay_pairH _ _)
      (fun _ => measurable_pairH _ _) (fun _ => rapidDecay_pairH _ _)

theorem rapidDecay_detK {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) :
    RapidDecay (detK e u) := rapidDecay_mconv one_ne_zero (rapidDecay_pairK _ _)
      (fun _ => measurable_pairK _ _) (fun _ => rapidDecay_pairK _ _)

/-- The real torus theta identity using the common determinant scale and the convolved pair.
Only one integrable weight on each side is needed for the log-coordinate averaging. -/
theorem determinant_theta_identity {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ)
    {F : (Fin (m + 1) → ℝ) → ℂ} (hF : Integrable F) {M Md : ℝ}
    (hM : Integrable (fun x => ‖weightedKernel e u F x‖ * detScale x ^ M))
    (hMd : Integrable (fun x => ‖weightedKernel e (-u) (fourierInvN F) x‖ * detScale x ^ Md))
    {a : ℝ} (ha : 0 < a) :
    theta volume (weightedKernel e u F) detScale (detH e u) a =
      (a : ℂ) * theta volume (weightedKernel e (-u) (fourierInvN F)) detScale (detK e u) a⁻¹ := by
  have hδm : ∀ i : Fin (m + 1), Measurable (fun x : Fin (m + 1) → ℝ => absPos (x i)) :=
    fun i => measurable_absPos.comp (measurable_pi_apply i)
  have hδ : ∀ (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ), 0 < absPos (x i) := fun _ _ => absPos_pos _
  have hH := theta_mconv volume (aestronglyMeasurable_weightedKernel e u hF.aestronglyMeasurable)
    hδm hδ (h := fun i => pairH (e i) (u i)) (fun _ => measurable_pairH _ _) (fun _ => rapidDecay_pairH _ _)
    hM (ε := 1) one_ne_zero ha
  have hK := theta_mconv volume (aestronglyMeasurable_weightedKernel e (-u)
    (continuous_fourierInvN hF).aestronglyMeasurable) hδm hδ
    (h := fun i => pairK (e i) (u i)) (fun _ => measurable_pairK _ _) (fun _ => rapidDecay_pairK _ _)
    hMd (ε := -1) (neg_ne_zero.2 one_ne_zero) (inv_pos.2 ha)
  change theta volume (weightedKernel e u F) detScale (detH e u) a = _ at hH
  change theta volume (weightedKernel e (-u) (fourierInvN F)) detScale
    (mconv (-1) (pairK (e 0) (u 0)) (fun j => pairK (e j.succ) (u j.succ))) a⁻¹ = _ at hK
  rw [funext (mconv_neg (1 : ℝ) (pairK (e 0) (u 0)) (fun j => pairK (e j.succ) (u j.succ)))] at hK
  rw [hH, detK, hK, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  have ht := torus_theta_identity e u (a := scale 1 a τ) (scale_pos 1 ha τ) hF
  rw [← Complex.ofReal_prod, prod_scale] at ht
  simp_rw [scale_inv] at ht
  simpa only [weightedKernel_mul_prod, kernelH, kernelK, Pi.neg_apply] using ht

/-- Product of the real Tate gamma factors for the torus characters. -/
def torusL {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ) (s : ℂ) : ℂ :=
  ∏ i, Gammaℝ (s + u i + (e i).val)

/-- Product of the real Tate root numbers for the positive Fourier sign. -/
def torusEpsilon {n : ℕ} (e : Fin n → Fin 2) : ℂ := ∏ i, I ^ (e i).val

theorem mellin_detH {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) (s : ℂ) :
    mellin (detH e u) (-s) = torusEpsilon e * Complex.exp (s ^ 2) ^ (m + 1) * (torusL e u s)⁻¹ := by
  unfold detH
  rw [mellin_mconv (measurable_pairH _ _) (fun _ => measurable_pairH _ _)
    (rapidDecay_pairH _ _) (fun _ => rapidDecay_pairH _ _)]
  rw [← Fin.prod_univ_succ (f := fun i => mellin (pairH (e i) (u i)) (-s))]
  simp only [mellin_pairH, pairMh, neg_sq, neg_neg]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, torusL, torusEpsilon]
  simp

theorem mellin_detK {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) (s : ℂ) :
    mellin (detK e u) (s - 1) = Complex.exp (s ^ 2) ^ (m + 1) * (torusL e (-u) (1 - s))⁻¹ := by
  unfold detK
  rw [mellin_mconv (measurable_pairK _ _) (fun _ => measurable_pairK _ _)
    (rapidDecay_pairK _ _) (fun _ => rapidDecay_pairK _ _)]
  rw [← Fin.prod_univ_succ (f := fun i => mellin (pairK (e i) (u i)) (s - 1))]
  simp only [mellin_pairK, pairMk, sub_eq_add_neg]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, torusL]
  simp

/-- Torus zeta integral, with the determinant scale to the complex power `s`. -/
def torusZeta {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ) (F : (Fin n → ℝ) → ℂ) (s : ℂ) : ℂ :=
  ∫ x, weightedKernel e u F x * (detScale x : ℂ) ^ s

private theorem torusL_ne_zero {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ)
    {s : ℂ} (hs : (∑ i, |(u i).re|) < s.re) : torusL e u s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => Gammaℝ_ne_zero_of_re_pos ?_
  have hi : |(u i).re| ≤ ∑ i, |(u i).re| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (u j).re) (Finset.mem_univ i)
  simp only [add_re, natCast_re]
  have h0 : (0 : ℝ) ≤ (e i).val := by positivity
  linarith [neg_abs_le (u i).re]

/-- Apply the spectral factors of the convolved real Tate pair to any two kernels
whose determinant theta transforms satisfy the reflection identity. -/
theorem determinant_pair_continuation {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ)
    {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    (μ : Measure X) (μ' : Measure X') [SFinite μ] [SFinite μ']
    {F : X → ℂ} {δ : X → ℝ} {F' : X' → ℂ} {δ' : X' → ℝ}
    (hF : AEStronglyMeasurable F μ) (hF' : AEStronglyMeasurable F' μ')
    (hδm : Measurable δ) (hδ'm : Measurable δ') (hδ : ∀ x, 0 < δ x) (hδ' : ∀ x, 0 < δ' x)
    (N : ℝ) (hN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F x‖ * δ x ^ σ) μ)
    (hNd : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖F' x‖ * δ' x ^ σ) μ')
    (hpair : ∀ a : ℝ, 0 < a → theta μ F δ (detH e u) a =
      (a : ℂ) * theta μ' F' δ' (detK e u) a⁻¹) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → (∫ x, F x * (δ x : ℂ) ^ s ∂μ) = M s) ∧
      (∀ s : ℂ, σ < s.re → (∫ x, F' x * (δ' x : ℂ) ^ s ∂μ') = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, torusL e u s * Md (1 - s) = torusEpsilon e * torusL e (-u) (1 - s) * M s := by
  let N₁ : ℝ := ∑ i, |(u i).re|
  have hH0 (s : ℂ) (hs : N₁ < s.re) : mellin (detH e u) (-s) ≠ 0 := by
    rw [mellin_detH]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ I_ne_zero)
      (pow_ne_zero _ (Complex.exp_ne_zero _))) (inv_ne_zero (torusL_ne_zero e u hs))
  have hK0 (s : ℂ) (hs : N₁ < s.re) : mellin (detK e u) (-s) ≠ 0 := by
    rw [show -s = (1 - s) - 1 by ring, mellin_detK, sub_sub_cancel]
    refine mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) (inv_ne_zero (torusL_ne_zero e (-u) ?_))
    simpa only [Pi.neg_apply, neg_re, abs_neg] using hs
  have hA : AnalyticOnNhd ℂ (fun s : ℂ => mellin (detH e u) (-s)) univ := fun s _ =>
    (((rapidDecay_detH e u).differentiable_mellin (measurable_detH e u).aestronglyMeasurable).comp
      differentiable_neg).analyticAt s
  have hB : AnalyticOnNhd ℂ (fun s : ℂ => mellin (detK e u) (s - 1)) univ := fun s _ =>
    (((rapidDecay_detK e u).differentiable_mellin (measurable_detK e u).aestronglyMeasurable).comp
      (differentiable_id.sub_const 1)).analyticAt s
  have ha0 := hA.preimage_zero_mem_codiscrete (x := ((N₁ + 1 : ℝ) : ℂ)) (hH0 _ (by simp))
  have hb0 := hB.preimage_zero_mem_codiscrete (x := (-((N₁ : ℝ) : ℂ))) (by
    simpa only [ofReal_add, ofReal_one, neg_add_rev, sub_eq_add_neg, add_comm] using
      hK0 ((N₁ + 1 : ℝ) : ℂ) (by simp))
  have hfac : ∀ᶠ s in codiscrete ℂ, torusL e u s * mellin (detH e u) (-s) =
      torusEpsilon e * 1 * torusL e (-u) (1 - s) * mellin (detK e u) (s - 1) := by
    filter_upwards [ha0, hb0] with s hs1 hs2
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hs1 hs2
    rw [mellin_detH] at hs1 ⊢
    rw [mellin_detK] at hs2 ⊢
    have h1 : torusL e u s ≠ 0 := fun h => by simp [h] at hs1
    have h2 : torusL e (-u) (1 - s) ≠ 0 := fun h => by simp [h] at hs2
    field_simp
  simpa only [mul_one] using exists_continuation μ μ' F δ F' δ' hF hF' hδm hδ'm hδ hδ'
    (detH e u) (detK e u) (measurable_detH e u) (measurable_detK e u)
    (rapidDecay_detH e u) (rapidDecay_detK e u) N hN hNd hpair N₁ hH0 hK0
    (fun s => ∫ x, F x * (δ x : ℂ) ^ s ∂μ) (fun s => ∫ x, F' x * (δ' x : ℂ) ^ s ∂μ')
    (torusL e u) (torusL e (-u)) (fun _ => 1) (torusEpsilon e) (fun _ _ => rfl) (fun _ _ => rfl) hfac

/-- Meromorphic continuation and the product Tate functional equation on one determinant scale,
assuming absolute convergence of the two weighted kernels on a right half-plane. -/
theorem torus_continuation {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ)
    {F : (Fin (m + 1) → ℝ) → ℂ} (hF : Integrable F) (N : ℝ)
    (hN : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖weightedKernel e u F x‖ * detScale x ^ σ))
    (hNd : ∀ σ : ℝ, N ≤ σ → Integrable (fun x => ‖weightedKernel e (-u) (fourierInvN F) x‖ * detScale x ^ σ)) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → torusZeta e u F s = M s) ∧
      (∀ s : ℂ, σ < s.re → torusZeta e (-u) (fourierInvN F) s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, torusL e u s * Md (1 - s) = torusEpsilon e * torusL e (-u) (1 - s) * M s :=
  determinant_pair_continuation e u volume volume
    (aestronglyMeasurable_weightedKernel e u hF.aestronglyMeasurable)
    (aestronglyMeasurable_weightedKernel e (-u) (continuous_fourierInvN hF).aestronglyMeasurable)
    measurable_detScale measurable_detScale detScale_pos detScale_pos N hN hNd
    (fun a ha => determinant_theta_identity e u hF (hN N le_rfl) (hNd N le_rfl) (a := a) ha)

/-! ### The case of Schwartz test functions -/

open scoped SchwartzMap FourierTransform RealInnerProductSpace

/-- The positive-sign Fourier transform on the real coordinate space, as a Schwartz map. -/
def schwartzFourierInvN {n : ℕ} (F : 𝓢(Fin n → ℝ, ℂ)) : 𝓢(Fin n → ℝ, ℂ) :=
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
    (𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e F))

theorem schwartzFourierInvN_apply {n : ℕ} (F : 𝓢(Fin n → ℝ, ℂ)) (y : Fin n → ℝ) :
    schwartzFourierInvN F y = fourierInvN F y := by
  unfold schwartzFourierInvN
  dsimp only
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourierInv_coe]
  rw [Real.fourierInv_eq', fourierInvN]
  refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
      (fun x => Complex.exp (2 * (π : ℂ) * I * ((∑ i, x i * y i : ℝ) : ℂ)) * F x))
  simp only [smul_eq_mul]
  congr 2
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change (↑(2 * π * ∑ i : Fin n, y i * x i : ℝ) : ℂ) * I =
    2 * (π : ℂ) * I * ((∑ i : Fin n, x i * y i : ℝ) : ℂ)
  rw [show (∑ i : Fin n, y i * x i) = ∑ i : Fin n, x i * y i from
    Finset.sum_congr rfl fun i _ => mul_comm _ _]
  push_cast
  ring

/-- For a Schwartz test, once the real part makes all coordinate exponents nonnegative,
absolute convergence follows from polynomially weighted Schwartz integrability. -/
theorem integrable_weightedKernel_schwartz {n : ℕ} (e : Fin n → Fin 2) (u : Fin n → ℂ)
    (F : 𝓢(Fin n → ℝ, ℂ)) (σ : ℝ) (hσ : ∀ i, 0 ≤ (u i).re - 1 + σ) :
    Integrable (fun x => ‖weightedKernel e u F x‖ * detScale x ^ σ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (∑ i, ((u i).re - 1 + σ))
  have hki (i : Fin n) : (u i).re - 1 + σ ≤ (k : ℝ) :=
    (Finset.single_le_sum (fun j _ => hσ j) (Finset.mem_univ i)).trans hk
  have hB : Integrable (fun x => ‖F x‖ + ‖x‖ ^ (k * n) * ‖F x‖) :=
    (F.integrable (μ := volume)).norm.add (F.integrable_pow_mul volume (k * n))
  have hm := (aestronglyMeasurable_weightedKernel e u F.continuous.aestronglyMeasurable).norm.mul
    (measurable_detScale.pow_const σ).aestronglyMeasurable
  refine hB.mono' hm (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (detScale_pos x).le _))]
  by_cases hx : ∀ i, x i ≠ 0
  · rw [weightedKernel, norm_mul, norm_prod, detScale,
      ← Real.finsetProd_rpow _ _ (fun i _ => (absPos_pos (x i)).le), mul_assoc, ← Finset.prod_mul_distrib]
    have h : (∏ i, ‖integrand (fun _ => 1) (e i) (u i) (x i)‖ * absPos (x i) ^ σ) ≤
        (max 1 ‖x‖) ^ (k * n) := by
      calc _ ≤ ∏ _ : Fin n, (max 1 ‖x‖) ^ k := by
             refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (norm_nonneg _)
               (Real.rpow_nonneg (absPos_pos (x i)).le _)) (fun i _ => ?_)
             rw [norm_integrand _ _ _ (hx i), norm_one, one_mul, absPos, ite_eq_right (hx i),
               ← Real.rpow_add (abs_pos.mpr (hx i)), ← Real.rpow_natCast]
             exact (Real.rpow_le_rpow (abs_nonneg _) ((Real.norm_eq_abs _).symm.le.trans
               ((norm_le_pi_norm x i).trans (le_max_right _ _))) (hσ i)).trans
               (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (hki i))
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    calc ‖F x‖ * _ ≤ ‖F x‖ * (max 1 ‖x‖) ^ (k * n) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ _ := by
        rcases le_total 1 ‖x‖ with h | h
        · rw [max_eq_right h, mul_comm]
          exact le_add_of_nonneg_left (norm_nonneg _)
        · rw [max_eq_left h, one_pow, mul_one]
          exact le_add_of_nonneg_right (by positivity)
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    have h0 : (∏ j, integrand (fun _ => 1) (e j) (u j) (x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [integrand, hi])
    simp only [weightedKernel, h0, mul_zero, norm_zero, zero_mul]
    positivity

/-- Meromorphic continuation and the functional equation for the determinant-scale torus zeta
integrals of a Schwartz test and its transform. -/
theorem schwartz_torus_continuation {m : ℕ} (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ)
    (F : 𝓢(Fin (m + 1) → ℝ, ℂ)) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → torusZeta e u F s = M s) ∧
      (∀ s : ℂ, σ < s.re → torusZeta e (-u) (fourierInvN F) s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, torusL e u s * Md (1 - s) = torusEpsilon e * torusL e (-u) (1 - s) * M s := by
  let N : ℝ := 1 + ∑ i, |(u i).re|
  have hN (σ : ℝ) (hσ : N ≤ σ) (i : Fin (m + 1)) : |(u i).re| + 1 ≤ σ := by
    have hi : |(u i).re| ≤ ∑ j, |(u j).re| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (u j).re) (Finset.mem_univ i)
    dsimp only [N] at hσ
    linarith
  refine torus_continuation e u F.integrable N (fun σ hσ => ?_) (fun σ hσ => ?_)
  · exact integrable_weightedKernel_schwartz e u F σ fun i => by
      linarith [hN σ hσ i, neg_abs_le (u i).re]
  · rw [← funext (schwartzFourierInvN_apply F)]
    exact integrable_weightedKernel_schwartz e (-u) (schwartzFourierInvN F) σ fun i => by
      simp only [Pi.neg_apply, neg_re]
      linarith [hN σ hσ i, le_abs_self (u i).re]

end Langlands.Global.RankinSelbergGlobal.ArchimedeanDeterminantTheta

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanMellinPair ArchimedeanTateTheta ArchimedeanDeterminantTheta
open scoped SchwartzMap

/-- The real torus theta identity at determinant scale, and the associated continuation and
functional equation for Schwartz test functions. -/
def ArchimedeanDeterminantThetaStatement : Prop :=
  (∀ (m : ℕ) (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ)
    (F : (Fin (m + 1) → ℝ) → ℂ) (M Md a : ℝ),
    Integrable F → Integrable (fun x => ‖weightedKernel e u F x‖ * detScale x ^ M) →
    Integrable (fun x => ‖weightedKernel e (-u) (fourierInvN F) x‖ * detScale x ^ Md) → 0 < a →
    theta volume (weightedKernel e u F) detScale (detH e u) a =
      (a : ℂ) * theta volume (weightedKernel e (-u) (fourierInvN F)) detScale (detK e u) a⁻¹) ∧
  (∀ (m : ℕ) (e : Fin (m + 1) → Fin 2) (u : Fin (m + 1) → ℂ) (F : 𝓢(Fin (m + 1) → ℝ, ℂ)),
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
      (∀ s : ℂ, σ < s.re → torusZeta e u F s = M s) ∧
      (∀ s : ℂ, σ < s.re → torusZeta e (-u) (fourierInvN F) s = Md s) ∧
      ∀ᶠ s in codiscrete ℂ, torusL e u s * Md (1 - s) = torusEpsilon e * torusL e (-u) (1 - s) * M s)

theorem archimedeanDeterminantTheta : ArchimedeanDeterminantThetaStatement :=
  ⟨fun _ e u _ _ _ _ hF hM hMd ha => determinant_theta_identity e u hF hM hMd ha,
    fun _ => schwartz_torus_continuation⟩

end Langlands.Global.RankinSelbergGlobal
