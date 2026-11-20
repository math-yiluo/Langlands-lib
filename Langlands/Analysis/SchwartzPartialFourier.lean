import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Partial Fourier transforms of Schwartz functions on a real product -/

noncomputable section

open MeasureTheory Filter Set Function
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzPartialFourier

section DominatedDerivatives

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace Y]
  {μ : Measure Y} {K : V → Y → ℂ}
  (F : (n : ℕ) → V → Y → V [×n]→L[ℝ] ℂ)
  (hI : ∀ n x, Integrable (F n x) μ)
  (hD : ∀ n x y, HasFDerivAt (fun z => F n z y)
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ (F (n + 1) x y)) x)
  (hB : ∀ n, ∃ b : Y → ℝ, Integrable b μ ∧ ∀ x y, ‖F (n + 1) x y‖ ≤ b y)

local instance (n : ℕ) : NormedAddCommGroup (V →L[ℝ] V [×n]→L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

include hI hD hB

private theorem hasFDerivAt_integral_family (n : ℕ) (x : V) :
    HasFDerivAt (fun z => ∫ y, F n z y ∂μ)
      (∫ y, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
        (F (n + 1) x y) ∂μ) x := by
  obtain ⟨b, hb, hle⟩ := hB n
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
  have hm : AEStronglyMeasurable (fun y => L (F (n + 1) x y)) μ :=
    L.continuous.comp_aestronglyMeasurable (hI (n + 1) x).aestronglyMeasurable
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun z y => L (F (n + 1) z y)) (s := univ) (bound := b)
    univ_mem (Eventually.of_forall fun z => (hI n z).aestronglyMeasurable)
    (hI n x) hm
    (ae_of_all _ fun y z _ => (L.norm_map _).trans_le (hle z y)) hb
    (ae_of_all _ fun y z _ => hD n z y)

private theorem iteratedFDeriv_integral_family
    (h₀ : ∀ x y v, F 0 x y v = K x y) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => ∫ y, K x y ∂μ) = fun x => ∫ y, F n x y ∂μ := by
  induction n with
  | zero =>
    funext x
    ext v
    rw [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.integral_apply (hI 0 x)]
    simp only [h₀]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    rw [Function.comp_apply, (hasFDerivAt_integral_family F hI hD hB n x).fderiv]
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ
    change L.symm (∫ y, L (F (n + 1) x y) ∂μ) = _
    let L' : (V [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×n]→L[ℝ] ℂ) :=
      L.toContinuousLinearEquiv.toContinuousLinearMap
    have he := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
      (E := V [×(n + 1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×n]→L[ℝ] ℂ) L' (hI (n + 1) x)
    change (∫ y, L (F (n + 1) x y) ∂μ) = L (∫ y, F (n + 1) x y ∂μ) at he
    rw [he, L.symm_apply_apply]

end DominatedDerivatives

private def expI (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem contDiff_expI : ContDiff ℝ ∞ expI :=
  (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

private theorem iteratedDeriv_expI (n : ℕ) : iteratedDeriv n expI =
    fun t => Complex.I ^ n * expI t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight (1 : ℂ)
      have hL : (L : ℝ → ℂ) = fun u : ℝ => (u : ℂ) := by
        funext u
        change u • (1 : ℂ) = _
        rw [Complex.real_smul, mul_one]
      rw [← hL]
      have h₁ : L 1 = 1 := (congrFun hL 1).trans Complex.ofReal_one
      simpa only [h₁] using (L.hasFDerivAt (x := t)).hasDerivAt
    have he := ((ht.mul_const Complex.I).cexp).const_mul (Complex.I ^ n)
    change deriv (fun t : ℝ => Complex.I ^ n * Complex.exp ((t : ℂ) * Complex.I)) t =
      Complex.I ^ (n + 1) * expI t
    rw [he.deriv, expI, pow_succ]
    ring

private theorem norm_iteratedFDeriv_expI (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n expI t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expI, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, expI, Complex.norm_exp]
  simp

section FirstCoordinate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private def phase (y : F) : E × F →L[ℝ] ℝ :=
  (-2 * Real.pi) • ((innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ E F))

private theorem phase_apply (y : F) (p : E × F) : phase y p = -2 * Real.pi * inner ℝ y p.2 :=
  rfl

private theorem norm_phase_le (y : F) : ‖phase (E := E) y‖ ≤ (2 * Real.pi) * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [phase_apply, neg_mul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (show 0 ≤ 2 * Real.pi by positivity)]
  calc
    _ ≤ (2 * Real.pi) * (‖y‖ * ‖p‖) :=
      mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm y p.2).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg y))) (by positivity)
    _ = _ := by ring

private theorem norm_phase_deriv_le (y : F) (p : E × F) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (expI ∘ phase y) p‖ ≤ ‖phase (E := E) y‖ ^ n := by
  rw [(phase y).iteratedFDeriv_comp_right contDiff_expI p (by simp)]
  simpa only [norm_iteratedFDeriv_expI, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
    using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n expI (phase y p)) (fun _ => phase (E := E) y)

private theorem iteratedFDeriv_affine {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : W → ℂ} (hf : ContDiff ℝ ∞ f)
    (A : V →L[ℝ] W) (b : W) (x : V) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z => f (A z + b)) x =
      (iteratedFDeriv ℝ n f (A x + b)).compContinuousLinearMap (fun _ => A) := by
  change iteratedFDeriv ℝ n ((fun z => f (z + b)) ∘ A) x = _
  have hg : ContDiff ℝ ∞ (fun z : W => f (z + b)) :=
    hf.comp (contDiff_id.add contDiff_const)
  rw [A.iteratedFDeriv_comp_right hg x (by simp), iteratedFDeriv_comp_add_right]

private def kernel (Φ : 𝓢(E × F, ℂ)) (p : E × F) (y : F) : ℂ :=
  Φ (p.1, y) * expI (phase y p)

private theorem contDiff_kernel (Φ : 𝓢(E × F, ℂ)) :
    ContDiff ℝ ∞ (fun q : (E × F) × F => kernel Φ q.1 q.2) := by
  refine ((Φ.smooth ⊤).comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).mul
    (contDiff_expI.comp ?_)
  simp only [phase_apply]
  exact contDiff_const.mul (contDiff_snd.inner ℝ (contDiff_snd.comp contDiff_fst))

private theorem contDiff_kernelAt (Φ : 𝓢(E × F, ℂ)) (y : F) :
    ContDiff ℝ ∞ (fun p : E × F => kernel Φ p y) :=
  (contDiff_kernel Φ).comp (contDiff_id.prodMk contDiff_const)

private def D (Φ : 𝓢(E × F, ℂ)) (n : ℕ) (p : E × F) (y : F) : (E × F) [×n]→L[ℝ] ℂ :=
  iteratedFDeriv ℝ n (fun z : E × F => kernel Φ z y) p

private theorem continuous_D (Φ : 𝓢(E × F, ℂ)) (n : ℕ) :
    Continuous (fun q : (E × F) × F => D Φ n q.1 q.2) := by
  let A : E × F →L[ℝ] (E × F) × F := ContinuousLinearMap.inl ℝ (E × F) F
  let Ψ := fun q : (E × F) × F => kernel Φ q.1 q.2
  have he (q : (E × F) × F) : D Φ n q.1 q.2 =
      (iteratedFDeriv ℝ n Ψ q).compContinuousLinearMap (fun _ => A) := by
    have hφ : (fun p : E × F => kernel Φ p q.2) = fun p => Ψ (A p + (0, q.2)) := by
      funext p
      simp [A, Ψ]
    have hs : ContDiff ℝ ∞ Ψ := contDiff_kernel Φ
    rw [D, hφ, iteratedFDeriv_affine hs A (0, q.2) q.1 n]
    simp [A]
  simp_rw [he]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => A)).continuous.comp
    ((contDiff_kernel Φ).continuous_iteratedFDeriv (by simp))

private theorem norm_slice_deriv_le (Φ : 𝓢(E × F, ℂ)) (p : E × F) (y : F) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : E × F => Φ (z.1, y)) p‖ ≤ ‖iteratedFDeriv ℝ i Φ (p.1, y)‖ := by
  let A : E × F →L[ℝ] E × F :=
    (ContinuousLinearMap.inl ℝ E F).comp (ContinuousLinearMap.fst ℝ E F)
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖(q.1, (0 : F))‖ ≤ 1 * ‖q‖
    simpa only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _), one_mul] using norm_fst_le q
  have he : (fun z : E × F => Φ (z.1, y)) = fun z => Φ (A z + (0, y)) := by
    funext z
    simp [A]
  rw [he, iteratedFDeriv_affine (Φ.smooth ⊤) A (0, y) p i]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i Φ (A p + (0, y))) (fun _ => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hp : A p + (0, y) = (p.1, y) := by simp [A]
  rw [hp] at hb ⊢
  calc
    _ ≤ _ := hb
    _ ≤ ‖iteratedFDeriv ℝ i Φ (p.1, y)‖ * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) hA) (norm_nonneg _)
    _ = _ := mul_one _

private theorem weighted_D_bound (Φ : 𝓢(E × F, ℂ)) (k n q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E × F) (y : F),
      ‖p.1‖ ^ k * ‖D Φ n p y‖ ≤ C * ((1 + ‖y‖) ^ q)⁻¹ := by
  let m := k + n + q
  let S : ℝ := 2 ^ m * ((Finset.Iic (m, n)).sup (fun j => SchwartzMap.seminorm ℝ j.1 j.2)) Φ
  let B : ℝ := max 1 (2 * Real.pi)
  let C : ℝ := (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * B ^ n * max S 0
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C, by dsimp only [C]; positivity, fun p y => ?_⟩
  let R := 1 + ‖(p.1, y)‖
  have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg _)
  have hphase (i : ℕ) (hi : i ≤ n) : ‖phase (E := E) y‖ ^ i ≤ (B * R) ^ n := by
    have hb : ‖phase (E := E) y‖ ≤ B * R := by
      refine (norm_phase_le (E := E) y).trans ?_
      gcongr
      · exact le_max_right _ _
      · exact (norm_snd_le (p.1, y)).trans (le_add_of_nonneg_left zero_le_one)
    exact (pow_le_pow_left₀ (norm_nonneg (phase (E := E) y)) hb i).trans
      (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hB hR) hi)
  have hΦ (i : ℕ) (hi : i ≤ n) : R ^ m * ‖iteratedFDeriv ℝ i Φ (p.1, y)‖ ≤ max S 0 :=
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, n)) le_rfl hi Φ
      (p.1, y)).trans (le_max_left _ _)
  have hS : ContDiff ℝ ∞ (fun z : E × F => Φ (z.1, y)) :=
    (Φ.smooth ⊤).comp (contDiff_fst.prodMk contDiff_const)
  have hP : ContDiff ℝ ∞ (expI ∘ phase (E := E) y) :=
    contDiff_expI.comp ((phase (E := E) y).contDiff)
  have hprod := norm_iteratedFDeriv_mul_le hS hP p (n := n) (by simp)
  change ‖D Φ n p y‖ ≤ _ at hprod
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  have hterms (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : E × F => Φ (z.1, y)) p‖ *
          ‖iteratedFDeriv ℝ (n - i) (expI ∘ phase y) p‖ * (‖p.1‖ ^ k * (1 + ‖y‖) ^ q) ≤
        (n.choose i : ℝ) * B ^ n * max S 0 := by
    have hX : ‖p.1‖ ≤ R := (norm_fst_le (p.1, y)).trans (le_add_of_nonneg_left zero_le_one)
    have hY : 1 + ‖y‖ ≤ R := by dsimp [R]; gcongr; exact norm_snd_le (p.1, y)
    calc
      _ ≤ (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i Φ (p.1, y)‖ * (B * R) ^ n *
          (R ^ k * R ^ q) := by
        gcongr
        · exact norm_slice_deriv_le Φ p y i
        · exact (norm_phase_deriv_le y p _).trans (hphase _ (Nat.sub_le _ _))
      _ = (n.choose i : ℝ) * B ^ n * (R ^ m * ‖iteratedFDeriv ℝ i Φ (p.1, y)‖) := by
        simp only [m, pow_add, mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hΦ i (by simpa using hi)) (by positivity)
  calc
    _ = ‖D Φ n p y‖ * (‖p.1‖ ^ k * (1 + ‖y‖) ^ q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
    _ ≤ C := by
      dsimp only [C]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_le_sum hterms

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

local instance (n : ℕ) : NormedAddCommGroup ((E × F) [×n]→L[ℝ] ℂ) :=
  ContinuousMultilinearMap.normedAddCommGroup

local instance (n : ℕ) : NormedSpace ℝ ((E × F) [×n]→L[ℝ] ℂ) :=
  ContinuousMultilinearMap.normedSpace

private def tail (y : F) : ℝ := ((1 + ‖y‖) ^ (Module.finrank ℝ F + 1))⁻¹

private theorem integrable_tail : Integrable (tail : F → ℝ) := by
  let q := Module.finrank ℝ F + 1
  have hq : (Module.finrank ℝ F : ℝ) < q := by
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ F)
  refine (integrable_one_add_norm hq).congr (ae_of_all _ fun y => ?_)
  simp only [tail, q, Real.rpow_neg (show 0 ≤ 1 + ‖y‖ by positivity), Real.rpow_natCast]

private theorem integrable_D (Φ : 𝓢(E × F, ℂ)) (n : ℕ) (p : E × F) :
    Integrable (D Φ n p) (volume : Measure F) := by
  obtain ⟨C, _, hC⟩ := weighted_D_bound Φ 0 n (Module.finrank ℝ F + 1)
  have hc : Continuous (D Φ n p) :=
    (continuous_D Φ n).comp (continuous_const.prodMk continuous_id)
  refine (integrable_tail.const_mul C).mono' hc.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  simpa only [pow_zero, one_mul, tail] using hC p y

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem hasFDerivAt_D (Φ : 𝓢(E × F, ℂ)) (n : ℕ) (p : E × F) (y : F) :
    HasFDerivAt (fun z => D Φ n z y)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E × F) ℂ
        (D Φ (n + 1) p y)) p := by
  have hs : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞ω) (fun z : E × F => kernel Φ z y) :=
    (contDiff_kernelAt Φ y).of_le (by simp)
  have hD := hs.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
  have h := (hD p).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at h
  exact h

private theorem dominated_next_D (Φ : 𝓢(E × F, ℂ)) (n : ℕ) :
    ∃ b : F → ℝ, Integrable b ∧ ∀ p y, ‖D Φ (n + 1) p y‖ ≤ b y := by
  obtain ⟨C, _, hC⟩ := weighted_D_bound Φ 0 (n + 1) (Module.finrank ℝ F + 1)
  simp only [pow_zero, one_mul] at hC
  exact ⟨fun y => C * tail y, integrable_tail.const_mul C, hC⟩

/-- Fourier transformation in the second coordinate, before bundling the result as Schwartz. -/
def partialIntegral (Φ : 𝓢(E × F, ℂ)) (p : E × F) : ℂ :=
  ∫ y, kernel Φ p y

theorem partialIntegral_eq (Φ : 𝓢(E × F, ℂ)) (p : E × F) :
    partialIntegral Φ p = 𝓕 (fun y : F => Φ (p.1, y)) p.2 := by
  rw [Real.fourier_eq']
  unfold partialIntegral
  apply integral_congr_ae
  filter_upwards with y
  rw [kernel, phase_apply, expI, smul_eq_mul, mul_comm]

private theorem iteratedFDeriv_partialIntegral (Φ : 𝓢(E × F, ℂ)) (n : ℕ) :
    iteratedFDeriv ℝ n (partialIntegral Φ) = fun p => ∫ y, D Φ n p y :=
  iteratedFDeriv_integral_family (D Φ) (integrable_D Φ) (hasFDerivAt_D Φ) (dominated_next_D Φ)
    (fun _p y v => iteratedFDeriv_zero_apply (f := fun p => kernel Φ p y) v) n

theorem contDiff_partialIntegral (Φ : 𝓢(E × F, ℂ)) : ContDiff ℝ ∞ (partialIntegral Φ) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  rw [iteratedFDeriv_partialIntegral]
  exact fun p => (hasFDerivAt_integral_family (D Φ) (integrable_D Φ)
    (hasFDerivAt_D Φ) (dominated_next_D Φ) n p).differentiableAt

/-- All derivatives of the partial integral decay rapidly in the fixed spatial coordinate. -/
theorem exists_weighted_deriv_le (Φ : 𝓢(E × F, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ p, ‖p.1‖ ^ k * ‖iteratedFDeriv ℝ n (partialIntegral Φ) p‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := weighted_D_bound Φ k n (Module.finrank ℝ F + 1)
  refine ⟨C * ∫ y : F, tail y, fun p => ?_⟩
  rw [iteratedFDeriv_partialIntegral, ← Real.norm_of_nonneg (pow_nonneg (norm_nonneg p.1) k),
    ← norm_smul, ← integral_smul, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => norm_nonneg _) (integrable_tail.const_mul C) ?_)
  refine ae_of_all _ fun y => ?_
  change ‖‖p.1‖ ^ k • D Φ n p y‖ ≤ C * tail y
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg p.1) k)]
  exact hC p y

end FirstCoordinate

section BothCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

private def fullFourier (Φ : 𝓢(E × F, ℂ)) : 𝓢(E × F, ℂ) :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ))

private theorem integrable_char_mul (Φ : 𝓢(E × F, ℂ)) {L : E × F → ℝ} (hL : Continuous L) :
    Integrable (fun p => Real.fourierChar (L p) • Φ p)
      ((volume : Measure E).prod (volume : Measure F)) := by
  have h : Integrable (Φ : E × F → ℂ) ((volume : Measure E).prod (volume : Measure F)) := Φ.integrable
  refine h.norm.mono' ((Real.continuous_fourierChar.comp hL).smul Φ.continuous).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

private theorem fullFourier_apply (Φ : 𝓢(E × F, ℂ)) (η : E) (ξ : F) :
    fullFourier Φ (η, ξ) = ∫ p : E × F,
      Real.fourierChar (-(inner ℝ p.1 η + inner ℝ p.2 ξ)) • Φ p := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  let Ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ
  let K := fun p : WithLp 2 (E × F) =>
    Real.fourierChar (-inner ℝ p (e.symm (η, ξ))) • Ψ p
  change (𝓕 Ψ) (e.symm (η, ξ)) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  calc
    (∫ p, K p) = ∫ p : E × F, K (e.symm p) := by
      exact ((WithLp.volume_preserving_toLp E F).integral_comp'
        (f := MeasurableEquiv.toLp 2 (E × F)) K).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      simp [K, Ψ, e, WithLp.prod_inner_apply]

private theorem fourier_first_partial (Φ : 𝓢(E × F, ℂ)) (ξ : F) :
    𝓕 (fun x : E => partialIntegral Φ (x, ξ)) = fun η => fullFourier Φ (η, ξ) := by
  funext η
  have hL : Continuous (fun p : E × F => -(inner ℝ p.1 η + inner ℝ p.2 ξ)) :=
    ((continuous_fst.inner continuous_const).add (continuous_snd.inner continuous_const)).neg
  have hI := integrable_char_mul Φ hL
  rw [Real.fourier_eq, fullFourier_apply, Measure.volume_eq_prod E F, integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards with x
  rw [partialIntegral_eq, Real.fourier_eq, Circle.smul_def, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [neg_add, AddChar.map_add_eq_mul, Circle.smul_def, mul_smul]

private theorem integrable_first_partial (Φ : 𝓢(E × F, ℂ)) (ξ : F) :
    Integrable (fun x : E => partialIntegral Φ (x, ξ)) := by
  have h := (integrable_char_mul Φ ((continuous_snd.inner continuous_const).neg :
    Continuous (fun p : E × F => -inner ℝ p.2 ξ))).integral_prod_left
  refine h.congr (ae_of_all _ fun x => ?_)
  change (∫ y : F, Real.fourierChar (-inner ℝ y ξ) • Φ (x, y)) = partialIntegral Φ (x, ξ)
  rw [partialIntegral_eq, Real.fourier_eq]

private def firstSlice (Φ : 𝓢(E × F, ℂ)) (ξ : F) : 𝓢(E, ℂ) := by
  let A : E →L[ℝ] E × F := ContinuousLinearMap.inl ℝ E F
  have hc : (fun x : E => (x, ξ)).HasTemperateGrowth := by
    have he : (fun x : E => (x, ξ)) = fun x => A x + (0, ξ) := by funext x; simp [A]
    rw [he]
    exact A.hasTemperateGrowth.add (HasTemperateGrowth.const _)
  exact SchwartzMap.compCLM ℂ hc ⟨1, 1, fun x => by
    rw [pow_one, one_mul]
    exact (norm_fst_le (x, ξ)).trans (le_add_of_nonneg_left zero_le_one)⟩ Φ

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem firstSlice_apply (Φ : 𝓢(E × F, ℂ)) (ξ : F) (x : E) :
    firstSlice Φ ξ x = Φ (x, ξ) := rfl

private def swappedFullFourier (Φ : 𝓢(E × F, ℂ)) : 𝓢(F × E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ F E) (fullFourier Φ)

private theorem partialIntegral_swap (Φ : 𝓢(E × F, ℂ)) (x : E) (ξ : F) :
    partialIntegral Φ (x, ξ) = partialIntegral (swappedFullFourier Φ) (ξ, -x) := by
  let f : E → ℂ := fun u => partialIntegral Φ (u, ξ)
  have hC : Continuous f := (contDiff_partialIntegral Φ).continuous.comp
    (continuous_id.prodMk continuous_const)
  have hfourier : 𝓕 f = fun η => fullFourier Φ (η, ξ) := fourier_first_partial Φ ξ
  have hslice : (firstSlice (fullFourier Φ) ξ : E → ℂ) = fun η => fullFourier Φ (η, ξ) :=
    funext (firstSlice_apply (fullFourier Φ) ξ)
  have hF : Integrable (𝓕 f) (volume : Measure E) := by
    rw [hfourier, ← hslice]
    exact (firstSlice (fullFourier Φ) ξ).integrable
  have h := congrFun (hC.fourierInv_fourier_eq (integrable_first_partial Φ ξ) hF) x
  change f x = _
  rw [← h, Real.fourierInv_eq_fourier_neg, partialIntegral_eq, hfourier]
  rfl

private def swapNeg : E × F →L[ℝ] F × E :=
  (ContinuousLinearMap.snd ℝ E F).prod (-(ContinuousLinearMap.fst ℝ E F))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
private theorem norm_swapNeg_le : ‖swapNeg (E := E) (F := F)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖(p.2, -p.1)‖ ≤ 1 * ‖p‖
  simp only [Prod.norm_def, norm_neg, one_mul, max_comm]
  exact le_rfl

private theorem exists_weighted_deriv_snd_le (Φ : 𝓢(E × F, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, ∀ p, ‖p.2‖ ^ k * ‖iteratedFDeriv ℝ n (partialIntegral Φ) p‖ ≤ C := by
  let Ψ := swappedFullFourier Φ
  let A := swapNeg (E := E) (F := F)
  obtain ⟨C, hC⟩ := exists_weighted_deriv_le Ψ k n
  refine ⟨C, fun p => ?_⟩
  have he : partialIntegral Φ = partialIntegral Ψ ∘ A := by
    funext q
    exact partialIntegral_swap Φ q.1 q.2
  rw [he, A.iteratedFDeriv_comp_right (contDiff_partialIntegral Ψ) p (by simp)]
  have hn : ‖A‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg A) norm_swapNeg_le
  have hL := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (partialIntegral Ψ) (A p)) (fun _ => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hL
  refine (mul_le_mul_of_nonneg_left (hL.trans ?_) (pow_nonneg (norm_nonneg _) _)).trans (hC (A p))
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _)

/-- The partial Fourier integral of a Schwartz function in its second variable is Schwartz. -/
def transform (Φ : 𝓢(E × F, ℂ)) : 𝓢(E × F, ℂ) where
  toFun := partialIntegral Φ
  smooth' := contDiff_partialIntegral Φ
  decay' k n := by
    obtain ⟨C, hC⟩ := exists_weighted_deriv_le Φ k n
    obtain ⟨D, hD⟩ := exists_weighted_deriv_snd_le Φ k n
    refine ⟨max C D, fun p => ?_⟩
    rw [Prod.norm_def]
    rcases le_total ‖p.1‖ ‖p.2‖ with h | h
    · rw [max_eq_right h]
      exact (hD p).trans (le_max_right _ _)
    · rw [max_eq_left h]
      exact (hC p).trans (le_max_left _ _)

@[simp]
theorem transform_apply (Φ : 𝓢(E × F, ℂ)) (x : E) (ξ : F) :
    transform Φ (x, ξ) = 𝓕 (fun y : F => Φ (x, y)) ξ :=
  partialIntegral_eq Φ (x, ξ)

end BothCoordinates

end Langlands.Analysis.SchwartzPartialFourier
