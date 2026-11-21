import Langlands.Analysis.CompactParameterSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Division of Schwartz functions by a linear form -/

noncomputable section

open Filter LineDeriv MeasureTheory Set
open scoped ContDiff LineDeriv SchwartzMap Topology unitInterval

set_option autoImplicit false

namespace Langlands.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The subspace of Schwartz functions vanishing on the kernel of a real linear form. -/
def schwartzVanishingOnKernel (ℓ : E →L[ℝ] ℝ) : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {f | ∀ x, ℓ x = 0 → f x = 0}
  zero_mem' := by simp
  add_mem' hf hg x hx := by simp [hf x hx, hg x hx]
  smul_mem' := by
    intro a f hf x hx
    simp [hf x hx]

namespace SchwartzLinearDivision

private def intervalAverage : C(I, ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ t : I, g t
      map_add' g h := integral_add
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' a g := integral_smul a (fun t : I => g t) }
    1 (fun g => by
      simp only [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := (volume : Measure I)) (ae_of_all _ g.norm_coe_le_norm))

private theorem intervalAverage_bound (g : C(I, ℂ)) : ‖intervalAverage g‖ ≤ ‖g‖ := by
  change ‖∫ t : I, g t‖ ≤ ‖g‖
  simpa using norm_integral_le_of_norm_le_const
    (μ := (volume : Measure I)) (ae_of_all _ g.norm_coe_le_norm)

variable (ℓ : E →L[ℝ] ℝ) (v : E)

private def segmentMap (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (1 - t) • ℓ.smulRight v

private theorem segmentMap_apply (t : ℝ) (x : E) :
    segmentMap ℓ v t x = x - ((1 - t) * ℓ x) • v := by
  simp [segmentMap, mul_smul]

private theorem contDiff_segmentMap_joint :
    ContDiff ℝ ∞ (fun p : E × ℝ => segmentMap ℓ v p.2 p.1) := by
  simp only [segmentMap_apply]
  fun_prop

private def transverseFamily (f : 𝓢(E, ℂ)) (x : E) : C(I, ℂ) :=
  ⟨fun t => ∂_{v} f (segmentMap ℓ v t x), by
    apply (SchwartzMap.continuous (∂_{v} f)).comp
    simp only [segmentMap_apply]
    fun_prop⟩

private theorem contDiff_transverseFamily (f : 𝓢(E, ℂ)) :
    ContDiff ℝ ∞ (transverseFamily ℓ v f) := by
  let coord : C(I, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  exact contDiffOn_univ.mp (contDiffOn_infty_compactFamily_of_joint coord
    isOpen_univ isOpen_univ (fun _ => mem_univ _)
    (h := fun p : E × ℝ => ∂_{v} f (segmentMap ℓ v p.2 p.1))
    (((∂_{v} f).smooth ⊤).comp (contDiff_segmentMap_joint ℓ v)).contDiffOn
    (fun _ _ _ => rfl))

private def smoothQuotient (f : 𝓢(E, ℂ)) (x : E) : ℂ :=
  intervalAverage (transverseFamily ℓ v f x)

private theorem smoothQuotient_eq_integral (f : 𝓢(E, ℂ)) (x : E) :
    smoothQuotient ℓ v f x = ∫ t in (0 : ℝ)..1, ∂_{v} f (segmentMap ℓ v t x) := by
  change (∫ t : I, ∂_{v} f (segmentMap ℓ v t x)) = _
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, ∂_{v} f (segmentMap ℓ v t x) :=
      integral_subtype measurableSet_Icc (fun t => ∂_{v} f (segmentMap ℓ v t x))
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

private theorem contDiff_smoothQuotient (f : 𝓢(E, ℂ)) :
    ContDiff ℝ ∞ (smoothQuotient ℓ v f) :=
  intervalAverage.contDiff.comp (contDiff_transverseFamily ℓ v f)

set_option backward.isDefEq.respectTransparency false in
private theorem smul_smoothQuotient (hv : ℓ v = 1) (f : schwartzVanishingOnKernel ℓ)
    (x : E) : ℓ x • smoothQuotient ℓ v f.val x = f.val x := by
  let curve (t : ℝ) := x - ℓ x • v + t • (ℓ x • v)
  have hcurve (t : ℝ) : curve t = segmentMap ℓ v t x := by
    dsimp [curve]
    rw [segmentMap_apply, sub_mul, one_mul, sub_smul, smul_smul, sub_sub_eq_add_sub]
    abel
  have hderiv (t : ℝ) :
      HasDerivAt (fun s => f.val (curve s)) (ℓ x • ∂_{v} f.val (curve t)) t := by
    have hc : HasDerivAt curve (ℓ x • v) t := by
      simpa only [curve, id, one_smul] using
        ((hasDerivAt_id t).smul_const (ℓ x • v)).const_add (x - ℓ x • v)
    simpa only [Function.comp_def, SchwartzMap.lineDerivOp_apply_eq_fderiv, map_smul] using
      (f.val.hasFDerivAt (curve t)).comp_hasDerivAt t hc
  have hContinuous : Continuous (fun t => ℓ x • ∂_{v} f.val (curve t)) := by
    have hc : Continuous curve := by unfold curve; fun_prop
    exact (continuous_const (y := ℓ x)).smul ((∂_{v} f.val).continuous.comp hc)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hContinuous.intervalIntegrable 0 1)
  have hz : f.val (curve 0) = 0 := f.property _ (by simp [curve, hv])
  have h1 : curve 1 = x := by simp [curve]
  rw [hz, h1, sub_zero] at hFTC
  rw [smoothQuotient_eq_integral, ← intervalIntegral.integral_smul]
  simp_rw [← hcurve]
  exact hFTC

private theorem norm_one_sub (t : I) : ‖1 - (t : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)]
  linarith [t.property.1]

private theorem norm_segmentMap_le (t : I) :
    ‖segmentMap ℓ v t‖ ≤ 1 + ‖ℓ‖ * ‖v‖ := by
  unfold segmentMap
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
  exact add_le_add ContinuousLinearMap.norm_id_le
    (mul_le_of_le_one_left (by positivity) (norm_one_sub t))

private theorem norm_le_segmentMap_add (t : I) {x : E} (hx : ‖ℓ x‖ ≤ 1) :
    ‖x‖ ≤ ‖segmentMap ℓ v t x‖ + ‖v‖ := by
  have h : ‖x‖ ≤ ‖segmentMap ℓ v t x‖ + ‖((1 - (t : ℝ)) * ℓ x) • v‖ := by
    simpa only [segmentMap_apply, sub_add_cancel] using
      norm_add_le (segmentMap ℓ v t x) (((1 - (t : ℝ)) * ℓ x) • v)
  refine h.trans (add_le_add_right ?_ _)
  rw [norm_smul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub t)).trans hx)

private theorem norm_iteratedFDeriv_transverse_le (f : 𝓢(E, ℂ)) (n : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ n ⇑(∂_{v} f : 𝓢(E, ℂ)) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) (f : E → ℂ) y‖ := by
  rw [show ⇑(∂_{v} f : 𝓢(E, ℂ)) = (fun z => fderiv ℝ f z v) from
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv v f)]
  rw [← norm_iteratedFDeriv_fderiv]
  have hf : ContDiff ℝ ∞ (fderiv ℝ (f : E → ℂ)) :=
    (f.smooth ⊤).fderiv_right (by simp)
  exact norm_iteratedFDeriv_clm_apply_const hf.contDiffAt (by simp)

private theorem weighted_iteratedFDeriv_smoothQuotient_le (f : 𝓢(E, ℂ)) (n : ℕ) (x : E)
    {weight bound : ℝ} (hw : 0 ≤ weight) (hb : 0 ≤ bound)
    (h : ∀ t : I, weight * ‖iteratedFDeriv ℝ n
      (⇑(∂_{v} f : 𝓢(E, ℂ)) ∘ segmentMap ℓ v t) x‖ ≤ bound) :
    weight * ‖iteratedFDeriv ℝ n (smoothQuotient ℓ v f) x‖ ≤ bound := by
  have hdiff := (contDiff_transverseFamily ℓ v f).contDiffAt (x := x)
  have hAvg : ‖intervalAverage‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun g => by
      simpa only [one_mul] using intervalAverage_bound g)
  have hComp := intervalAverage.norm_iteratedFDeriv_comp_left hdiff (n := n) (by simp)
  have hFamily :
      ‖weight • iteratedFDeriv ℝ n (transverseFamily ℓ v f) x‖ ≤ bound := by
    apply ContinuousMultilinearMap.opNorm_le_bound hb
    intro m
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have heval := (ContinuousMap.evalCLM (R := ℝ) (M := ℂ) t).iteratedFDeriv_comp_left
      hdiff (i := n) (by simp)
    have hValue :
        iteratedFDeriv ℝ n (⇑(∂_{v} f : 𝓢(E, ℂ)) ∘ segmentMap ℓ v t) x m =
          (iteratedFDeriv ℝ n (transverseFamily ℓ v f) x m) t :=
      congrArg (fun d => d m) heval
    simp only [smul_apply, ContinuousMap.smul_apply,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, ← hValue]
    calc
      _ ≤ weight * (‖iteratedFDeriv ℝ n (⇑(∂_{v} f : 𝓢(E, ℂ)) ∘ segmentMap ℓ v t) x‖ *
          ∏ i, ‖m i‖) := mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.le_opNorm _ _) hw
      _ ≤ _ := by rw [← mul_assoc]; gcongr; exact h t
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw] at hFamily
  refine le_trans ?_ hFamily
  apply mul_le_mul_of_nonneg_left _ hw
  exact hComp.trans (mul_le_of_le_one_left (norm_nonneg _) hAvg)

private theorem near_kernel_bound (f : 𝓢(E, ℂ)) (k n : ℕ) (x : E) (hx : ‖ℓ x‖ ≤ 1) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (smoothQuotient ℓ v f) x‖ ≤
      ((1 + ‖v‖) ^ k * ‖v‖ * (1 + ‖ℓ‖ * ‖v‖) ^ n * 2 ^ k) *
        (Finset.Iic (k, n + 1)).sup (schwartzSeminormFamily ℂ E ℂ) f := by
  apply weighted_iteratedFDeriv_smoothQuotient_le ℓ v f n x (by positivity)
    (mul_nonneg (by positivity) (apply_nonneg _ _))
  intro t
  let A := segmentMap ℓ v t
  have hxA : ‖x‖ ≤ (1 + ‖v‖) * (1 + ‖A x‖) := by
    calc
      ‖x‖ ≤ ‖A x‖ + ‖v‖ := norm_le_segmentMap_add ℓ v t hx
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg (A x))]
  have hComp : ‖iteratedFDeriv ℝ n (⇑(∂_{v} f : 𝓢(E, ℂ)) ∘ A) x‖ ≤
      ‖iteratedFDeriv ℝ n ⇑(∂_{v} f : 𝓢(E, ℂ)) (A x)‖ * ‖A‖ ^ n := by
    rw [A.iteratedFDeriv_comp_right ((∂_{v} f).smooth ⊤) x (by simp)]
    simpa using
      (iteratedFDeriv ℝ n ⇑(∂_{v} f : 𝓢(E, ℂ)) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
  calc
    _ ≤ ((1 + ‖v‖) * (1 + ‖A x‖)) ^ k *
        ((‖v‖ * ‖iteratedFDeriv ℝ (n + 1) (f : E → ℂ) (A x)‖) *
          (1 + ‖ℓ‖ * ‖v‖) ^ n) := by
      change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(∂_{v} f : 𝓢(E, ℂ)) ∘ A) x‖ ≤ _
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxA _)
        (hComp.trans (mul_le_mul (norm_iteratedFDeriv_transverse_le v f n (A x))
          (pow_le_pow_left₀ (norm_nonneg _) (norm_segmentMap_le ℓ v t) _)
          (by positivity) (by positivity))) (by positivity) (by positivity)
    _ = ((1 + ‖v‖) ^ k * ‖v‖ * (1 + ‖ℓ‖ * ‖v‖) ^ n) *
        ((1 + ‖A x‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) (f : E → ℂ) (A x)‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := by
      rw [mul_assoc _ (2 ^ k)]
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n + 1))
          le_rfl le_rfl f (A x)) (by positivity)

private theorem norm_iteratedFDerivWithin_inv_le (i : ℕ) (x : E) (hx : 1 ≤ ‖ℓ x‖) :
    ‖iteratedFDerivWithin ℝ i (fun y => (ℓ y)⁻¹) (ℓ ⁻¹' ({0}ᶜ : Set ℝ)) x‖ ≤
      (i.factorial : ℝ) * ‖ℓ‖ ^ i := by
  have hx' : ℓ x ∈ ({0}ᶜ : Set ℝ) := by
    simp only [mem_compl_iff, mem_singleton_iff]
    intro heq
    rw [heq, norm_zero] at hx
    exact (not_le_of_gt zero_lt_one) hx
  have hopen : IsOpen ({0}ᶜ : Set ℝ) := isClosed_singleton.isOpen_compl
  have hinv : ContDiffOn ℝ ∞ (Inv.inv : ℝ → ℝ) {0}ᶜ := contDiffOn_inv ℝ
  change ‖iteratedFDerivWithin ℝ i (Inv.inv ∘ ℓ) (ℓ ⁻¹' ({0}ᶜ : Set ℝ)) x‖ ≤ _
  rw [ℓ.iteratedFDerivWithin_comp_right hinv hopen.uniqueDiffOn
    (hopen.preimage ℓ.continuous).uniqueDiffOn hx' (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    iteratedFDerivWithin_of_isOpen i hopen hx', norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast, norm_zpow]
  gcongr
  exact (mul_le_mul_of_nonneg_left (zpow_le_one_of_nonpos₀ hx (by omega)) (by positivity)).trans_eq
    (mul_one _)

open scoped BigOperators in
private theorem away_kernel_bound (hv : ℓ v = 1) (f : schwartzVanishingOnKernel ℓ)
    (k n : ℕ) (x : E) (hx : 1 ≤ ‖ℓ x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (smoothQuotient ℓ v f.val) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i.factorial : ℝ) * ‖ℓ‖ ^ i)) *
        (Finset.Iic (k, n + 1)).sup (schwartzSeminormFamily ℂ E ℂ) f.val := by
  let U := ℓ ⁻¹' ({0}ᶜ : Set ℝ)
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage ℓ.continuous
  have hxU : x ∈ U := by
    change ℓ x ≠ 0
    intro heq
    rw [heq, norm_zero] at hx
    exact (not_le_of_gt zero_lt_one) hx
  have hinv : ContDiffOn ℝ ∞ (fun y => (ℓ y)⁻¹) U :=
    (contDiffOn_inv ℝ).comp_continuousLinearMap ℓ
  have hEq : EqOn (smoothQuotient ℓ v f.val) (fun y => (ℓ y)⁻¹ • f.val y) U := fun y hy =>
    (eq_inv_smul_iff₀ (show ℓ y ≠ 0 from hy)).mpr (smul_smoothQuotient ℓ v hv f y)
  rw [← iteratedFDerivWithin_of_isOpen n hU hxU,
    iteratedFDerivWithin_congr hEq hxU]
  have hProduct := norm_iteratedFDerivWithin_smul_le hinv (f.val.smooth ⊤).contDiffOn
    hU.uniqueDiffOn hxU (n := n) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hxU (f := ⇑f.val)] at hProduct
  calc
    _ ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun y => (ℓ y)⁻¹) U x‖ *
          ‖iteratedFDeriv ℝ (n - i) f.val x‖) :=
      mul_le_mul_of_nonneg_left hProduct (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun y => (ℓ y)⁻¹) U x‖) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f.val x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      gcongr
      · exact norm_iteratedFDerivWithin_inv_le ℓ i x hx
      · refine (SchwartzMap.le_seminorm ℂ k (n - i) f.val x).trans ?_
        exact Seminorm.le_def.mp
          (Finset.le_sup (f := schwartzSeminormFamily ℂ E ℂ)
            (Finset.mem_Iic.mpr (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩))) f.val

open scoped BigOperators in
private theorem exists_decay_bound (hv : ℓ v = 1) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : schwartzVanishingOnKernel ℓ) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (smoothQuotient ℓ v f.val) x‖ ≤
        C * (Finset.Iic (k, n + 1)).sup (schwartzSeminormFamily ℂ E ℂ) f.val := by
  let C₁ : ℝ := (1 + ‖v‖) ^ k * ‖v‖ * (1 + ‖ℓ‖ * ‖v‖) ^ n * 2 ^ k
  let C₂ : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i.factorial : ℝ) * ‖ℓ‖ ^ i)
  refine ⟨max C₁ C₂, le_trans (show 0 ≤ C₁ by dsimp [C₁]; positivity) (le_max_left _ _),
    fun f x => ?_⟩
  rcases le_total ‖ℓ x‖ 1 with hx | hx
  · exact (near_kernel_bound ℓ v f.val k n x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg _ _))
  · exact (away_kernel_bound ℓ v hv f k n x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg _ _))

private def quotientSchwartzMap (hv : ℓ v = 1) (f : schwartzVanishingOnKernel ℓ) : 𝓢(E, ℂ) :=
  { toFun := smoothQuotient ℓ v f.val
    smooth' := contDiff_smoothQuotient ℓ v f.val
    decay' := by
      intro k n
      obtain ⟨C, _, hC⟩ := exists_decay_bound ℓ v hv k n
      exact ⟨_, hC f⟩ }

private def quotientLinearMap (hv : ℓ v = 1) : schwartzVanishingOnKernel ℓ →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun := quotientSchwartzMap ℓ v hv
  map_add' f g := by
    ext x
    change (∫ t : I, ∂_{v} (f.val + g.val) (segmentMap ℓ v t x)) =
      (∫ t : I, ∂_{v} f.val (segmentMap ℓ v t x)) + (∫ t : I, ∂_{v} g.val (segmentMap ℓ v t x))
    simp only [lineDerivOp_add, add_apply]
    exact integral_add
      ((transverseFamily ℓ v f.val x).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((transverseFamily ℓ v g.val x).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  map_smul' a f := by
    ext x
    change (∫ t : I, ∂_{v} (a • f.val) (segmentMap ℓ v t x)) =
      a • (∫ t : I, ∂_{v} f.val (segmentMap ℓ v t x))
    simp only [lineDerivOp_smul, smul_apply]
    exact integral_smul a (fun t : I => ∂_{v} f.val (segmentMap ℓ v t x))

private def quotientCLM (hv : ℓ v = 1) : schwartzVanishingOnKernel ℓ →L[ℂ] 𝓢(E, ℂ) where
  toLinearMap := quotientLinearMap ℓ v hv
  cont := by
    let q := schwartzSeminormFamily ℂ E ℂ
    let ι := (schwartzVanishingOnKernel ℓ).subtype
    have hq : WithSeminorms q := schwartz_withSeminorms ℂ E ℂ
    have hp : WithSeminorms (q.comp ι) :=
      Topology.IsInducing.withSeminorms (f := ι) hq .subtypeVal
    refine WithSeminorms.continuous_of_isBounded hp hq _ (Seminorm.IsBounded.of_real ?_)
    rintro ⟨k, n⟩
    obtain ⟨C, hC, hb⟩ := exists_decay_bound ℓ v hv k n
    refine ⟨Finset.Iic (k, n + 1), C, fun f => ?_⟩
    rw [← SeminormFamily.finset_sup_comp]
    exact SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC (apply_nonneg _ _)) (hb f)

private theorem exists_transverse_vector (hℓ : ℓ ≠ 0) : ∃ v : E, ℓ v = 1 := by
  obtain ⟨x, hx⟩ : ∃ x : E, ℓ x ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext h)
  exact ⟨(ℓ x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩

end SchwartzLinearDivision

/-- Continuous complex-linear division by a nonzero real linear form, on Schwartz functions
that vanish on its kernel. -/
def schwartzLinearDivision (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    schwartzVanishingOnKernel ℓ →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzLinearDivision.quotientCLM ℓ (SchwartzLinearDivision.exists_transverse_vector ℓ hℓ).choose
    (SchwartzLinearDivision.exists_transverse_vector ℓ hℓ).choose_spec

/-- Division by the linear form recovers the input after pointwise multiplication by the form. -/
theorem smul_schwartzLinearDivision_apply (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (f : schwartzVanishingOnKernel ℓ) (x : E) :
    ℓ x • schwartzLinearDivision ℓ hℓ f x = f.val x :=
  SchwartzLinearDivision.smul_smoothQuotient ℓ _
    (SchwartzLinearDivision.exists_transverse_vector ℓ hℓ).choose_spec f x

end Langlands.Analysis
