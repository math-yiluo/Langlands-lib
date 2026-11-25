import Langlands.Theta.Real.BigCellOperator

/-!
# Derivatives in `L²` of the big-cell operator families (internal)

`HasL2DerivAt U Q t₀`: a family `U t` of operators of Schwartz space has, at `t₀`, the derivative
`Q` in the sense that `t ↦ (U t f) ∈ L²` has derivative `(Q f) ∈ L²` for every `f`. Products,
scalar multiples and constants behave as expected (`HasL2DerivAt.mul`, `.smul`, `.const`), and the
families `chirp (S t)`, `dilation (B t)` and `bigCellOp (A t) (B t) (C t) (c t)` have such
derivatives, given by the multiplication operators `quadMul` and the vector-field derivatives
`vectorFieldDeriv` (`hasL2DerivAt_chirp`, `hasL2DerivAt_dilation`, `hasL2DerivAt_bigCellOp`).
For a family that conjugates the derived Schrödinger operators along a smooth family of linear
maps, such a derivative at `0` is a derivative of Schwartz functions pointwise
(`HasL2DerivAt.hasDerivAt`). Everything here is internal to `Langlands.Theta.Real.LocalLift`
and the metaplectic group.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real RealInnerProductSpace FourierTransform

namespace Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l]


theorem exists_decay {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : SchwartzMap (EuclideanSpace ℝ l) F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h := fun x => one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g x
  simp only [norm_iteratedFDeriv_zero] at h
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

theorem csmul (r : ℝ) (x : RealL2 l) : (r : ℂ) • x = r • x := by
  rw [coe_smul]
  rfl

theorem hasDerivAt_schwartz_to_L2 {F : ℝ → RealSchwartz l} {G : RealSchwartz l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C', hC', hG⟩ := exists_decay G N
  let u : ℝ → RealSchwartz l := fun t => (((t - t₀)⁻¹ : ℝ) : ℂ) • (F t - F t₀) - G
  have hu : ∀ t x, u t x = (t - t₀)⁻¹ • (F t x - F t₀ x) - G x := fun t x => by
    simp [u]
  have h1 : Tendsto (fun t => ∫ x, ‖u t x‖ ^ (2 : ℝ)) (𝓝[≠] t₀) (𝓝 (∫ _x : EuclideanSpace ℝ l, (0 : ℝ))) := by
    have hi := (integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := N)
      (by rw [hN]; push_cast; linarith)).const_mul ((C + C') ^ 2)
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun t => ((u t).continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable) ?_ hi
      (.of_forall fun x => ?_)
    · filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with t ht ht0
      refine .of_forall fun x => ?_
      have ht1 : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 ht0)
      have hw : 1 ≤ (1 + ‖x‖) ^ N := one_le_pow₀ (by simp)
      have h2 : (1 + ‖x‖) ^ N * ‖u t x‖ ≤ C + C' := by
        rw [hu]
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
        rw [mul_add, norm_smul, norm_inv, Real.norm_eq_abs]
        refine add_le_add ?_ (hG x)
        rw [mul_left_comm, inv_mul_le_iff₀ ht1, mul_comm |t - t₀|]
        exact ht x
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity),
        ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h3 : ((1 + ‖x‖) ^ N * ‖u t x‖) ^ 2 ≤ (C + C') ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      refine le_trans ?_ h3
      rw [mul_pow, mul_comm]
      gcongr
      nlinarith
    · have h2 := (hasDerivAt_iff_tendsto_slope.1 (hp x))
      have h3 := tendsto_iff_norm_sub_tendsto_zero.1 h2
      have h4 := h3.rpow_const (p := 2) (Or.inr (by norm_num))
      simpa [hu, slope_def_module] using h4
  rw [integral_zero] at h1
  have h2 := h1.rpow_const (p := 2⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr fun t => ?_
  have : slope (fun t => schwartzToL2 l (F t)) t₀ t - schwartzToL2 l G = (u t).toLp 2 volume := by
    rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), slope_def_module]
    simp only [u, map_sub, map_smul]
    simp only [csmul]
  rw [this, norm_toLp' (by simp) (by simp)]
  simp

def HasL2DerivAt (U : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l) (Q : RealSchwartz l → RealSchwartz l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀

theorem HasL2DerivAt.const (U : RealSchwartz l →L[ℂ] RealSchwartz l) (t₀ : ℝ) : HasL2DerivAt (fun _ => U) (fun _ => 0) t₀ := fun f => by
  simpa [-SchwartzMap.toLpCLM_apply] using hasDerivAt_const t₀ (schwartzToL2 l (U f))

theorem HasL2DerivAt.smul {U : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l} {Q : RealSchwartz l → RealSchwartz l} {t₀ : ℝ} (h : HasL2DerivAt U Q t₀) {c : ℝ → ℂ} {c' : ℂ}
    (hc : HasDerivAt c c' t₀) : HasL2DerivAt (fun t => c t • U t) (fun f => c t₀ • Q f + c' • U t₀ f) t₀ := fun f => by
  simpa [-SchwartzMap.toLpCLM_apply] using hc.fun_smul (h f)

theorem HasL2DerivAt.mul {U W : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l} {P Q : RealSchwartz l → RealSchwartz l} {t₀ : ℝ} (hU : HasL2DerivAt U P t₀) (hW : HasL2DerivAt W Q t₀)
    (hn : ∀ᶠ t in 𝓝 t₀, ∀ f, ‖schwartzToL2 l (U t f)‖ = ‖schwartzToL2 l f‖) :
    HasL2DerivAt (fun t => U t * W t) (fun f => P (W t₀ f) + U t₀ (Q f)) t₀ := fun f => by
  have h1 : HasDerivAt (fun t => schwartzToL2 l (U t (W t f - W t₀ f - ((t - t₀ : ℝ) : ℂ) • Q f))) 0 t₀ := by
    have h := (hW f).isLittleO
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_) h
    filter_upwards [hn] with t ht
    simp only [sub_self, ofReal_zero, zero_smul, map_zero, smul_zero, sub_zero, ht, one_mul]
    simp only [map_sub, map_smul]
    simp only [csmul, le_refl]
  have h2 : HasDerivAt (fun t : ℝ => (t - t₀) • schwartzToL2 l (U t (Q f))) (schwartzToL2 l (U t₀ (Q f))) t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).fun_smul (hU (Q f))
  have h3 := (h1.fun_add h2).fun_add (hU (W t₀ f))
  rw [zero_add, ← map_add, add_comm (U t₀ (Q f))] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun t => ?_)
  simp only [mul_apply_eq_comp, map_sub, map_smul]
  simp only [csmul]
  abel

variable [DecidableEq l]

theorem weyl_step {V : RealSchwartz l →L[ℂ] RealSchwartz l} {w v : l ⊕ l → ℝ} (h : ∀ f, schrodingerDeriv w (V f) = V (schrodingerDeriv v f))
    (A : RealSchwartz l →L[ℂ] RealSchwartz l) (f : RealSchwartz l) :
    schwartzToL2 l ((A * schrodingerDeriv w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (schrodingerDeriv (Pi.single a 1) f))) := by
  rw [mul_apply_eq_comp, h, schrodingerDeriv_eq_sum v]
  simp only [_root_.sum_apply, _root_.smul_apply, map_sum, map_smul]
  simp only [csmul]

theorem HasL2DerivAt.differentiableAt {V : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l} {Q : RealSchwartz l → RealSchwartz l} {t₀ : ℝ} (hV : HasL2DerivAt V Q t₀)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv : ∀ w a, DifferentiableAt ℝ (fun t => v t w a) t₀)
    (h : ∀ᶠ t in 𝓝 t₀, ∀ w f, schrodingerDeriv w (V t f) = V t (schrodingerDeriv (v t w) f)) (f : RealSchwartz l) (lam : RealSchwartz l →L[ℂ] ℂ) :
    DifferentiableAt ℝ (fun t => lam (V t f)) t₀ := by
  have key : ∀ A ∈ weylAlgebra l, ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀ := fun A hA => by
    refine weylAlgebra_induction (P := fun A => ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀)
      (fun f => (hV f).differentiableAt) ?_ (fun f => by simp) ?_ ?_ hA
    · intro A w ih f
      refine (DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (schrodingerDeriv (Pi.single a 1) f))).congr_of_eventuallyEq ?_
      filter_upwards [h] with t ht
      exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [_root_.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [_root_.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor_through_toLp lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).differentiableAt.comp t₀ (differentiableAt_pi.2 fun i => key _ (hA i) f)

theorem HasL2DerivAt.hasDerivAt {V : ℝ → RealSchwartz l →L[ℂ] RealSchwartz l} {Q : RealSchwartz l →L[ℂ] RealSchwartz l} (hV : HasL2DerivAt V Q 0) (h0 : ∀ f, V 0 f = f)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (v' : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv0 : ∀ w, v 0 w = w)
    (hv : ∀ w a, HasDerivAt (fun t => v t w a) (-v' w a) 0) (hQ : ∀ w, Q * schrodingerDeriv w - schrodingerDeriv w * Q = schrodingerDeriv (v' w))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w f, schrodingerDeriv w (V t f) = V t (schrodingerDeriv (v t w) f)) (f : RealSchwartz l) (lam : RealSchwartz l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (V t f)) (lam (Q f)) 0 := by
  have key : ∀ A ∈ weylAlgebra l, ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0 := fun A hA => by
    refine weylAlgebra_induction (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0)
      hV ?_ (fun f => by simpa [-SchwartzMap.toLpCLM_apply] using hasDerivAt_const _ _) ?_ ?_ hA
    · intro A w ih f
      refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (schrodingerDeriv (Pi.single a 1) f))).congr_deriv ?_).congr_of_eventuallyEq ?_
      · have e : schrodingerDeriv w * Q = Q * schrodingerDeriv w - schrodingerDeriv (v' w) := by rw [← hQ, sub_sub_cancel]
        rw [mul_apply_eq_comp, ← mul_apply_eq_comp (schrodingerDeriv w), e, schrodingerDeriv_eq_sum w,
          schrodingerDeriv_eq_sum (v' w)]
        simp only [_root_.sum_apply, _root_.smul_apply, map_sum, map_smul, hv0, h0,
          _root_.sub_apply, mul_apply_eq_comp, map_sub, neg_smul, ← sub_eq_add_neg,
          Finset.sum_sub_distrib]
        simp only [csmul]
      · filter_upwards [h] with t ht
        exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [_root_.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [_root_.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor_through_toLp lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.2 fun i => key _ (hA i) f)



def quadMul (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  smulLeftCLM ℂ fun x : EuclideanSpace ℝ l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I

omit [DecidableEq l] in
theorem quadMul_apply (S : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) : quadMul S f x = ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I * f x := by
  have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => -π * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I :=
    (ofRealCLM.hasTemperateGrowth.comp h2).mul (Function.HasTemperateGrowth.const _)
  rw [quadMul, smulLeftCLM_apply_apply h3, smul_eq_mul]

theorem norm_exp_sub_le (a b : ℝ) : ‖exp ((a : ℂ) * I) - exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have : exp ((a : ℂ) * I) - exp ((b : ℂ) * I) = exp ((b : ℂ) * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem exists_lip {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ → F} {S' : F} {t₀ : ℝ}
    (h : HasDerivAt S S' t₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in 𝓝 t₀, ‖S t - S t₀‖ ≤ K * |t - t₀| := by
  obtain ⟨K, hK, h⟩ := h.isBigO_sub.exists_nonneg
  exact ⟨K, hK, h.bound⟩

omit [DecidableEq l] in
theorem hasL2DerivAt_chirp {S : ℝ → EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {S' : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {t₀ : ℝ} (h : HasDerivAt S S' t₀) :
    HasL2DerivAt (fun t => chirp (S t)) (fun f => quadMul S' (chirp (S t₀) f)) t₀ := fun f => by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay f (N + 2)
  refine hasDerivAt_schwartz_to_L2 (C := π * K * C) (fun x => ?_) ?_
  · simp only [chirp_apply, quadMul_apply]
    have h1 : HasDerivAt (fun t => S t x) (S' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 : HasDerivAt (fun t => ⟪x, S t x⟫) ⟪x, S' x⟫ t₀ := (innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t₀ h1
    exact (((h2.const_mul (-π)).ofReal_comp.mul_const I).cexp.mul_const (f x)).congr_deriv (by ring)
  · filter_upwards [hb] with t ht x
    rw [← hN]
    simp only [chirp_apply]
    rw [← sub_mul, norm_mul]
    have h1 : |-π * ⟪x, S t x⟫ - -π * ⟪x, S t₀ x⟫| ≤ π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) := by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_neg, abs_of_pos Real.pi_pos, ← _root_.sub_apply]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) Real.pi_pos.le
      have h2 := (S t - S t₀).le_opNorm x
      calc ‖x‖ * ‖(S t - S t₀) x‖ ≤ ‖x‖ * ((K * |t - t₀|) * ‖x‖) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (norm_nonneg _)
            gcongr
        _ = ‖x‖ ^ 2 * (K * |t - t₀|) := by ring
        _ ≤ _ := by gcongr; simp
    calc _ ≤ (1 + ‖x‖) ^ N * (π * ((1 + ‖x‖) ^ 2 * (K * |t - t₀|)) * ‖f x‖) := by
          gcongr
          exact (norm_exp_sub_le _ _).trans h1
      _ = π * K * ((1 + ‖x‖) ^ (N + 2) * ‖f x‖) * |t - t₀| := by ring
      _ ≤ _ := by gcongr; exact hf x

def vectorFieldDeriv (H : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (f : RealSchwartz l) : RealSchwartz l :=
  bilinLeftCLM (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ l →L[ℝ] ℂ)) H.hasTemperateGrowth (fderivCLM ℝ (EuclideanSpace ℝ l) ℂ f)

omit [DecidableEq l] in
theorem vectorFieldDeriv_apply (H : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l) (f : RealSchwartz l) (x : EuclideanSpace ℝ l) : vectorFieldDeriv H f x = fderiv ℝ f x (H x) := rfl

omit [DecidableEq l] in
theorem hasL2DerivAt_dilation_one {H : ℝ → EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {H' : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : RealSchwartz l) {F : ℝ → RealSchwartz l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vectorFieldDeriv H' f)) t₀ := by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay (fderivCLM ℝ (EuclideanSpace ℝ l) ℂ f) (N + 1)
  refine hasDerivAt_schwartz_to_L2 (C := 2 ^ (N + 1) * C * K) (fun x => ?_) ?_
  · have h1 : HasDerivAt (fun t => H t x) (H' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 := (f.hasFDerivAt (H t₀ x)).comp_hasDerivAt t₀ h1
    rw [h0] at h2
    exact h2.congr_of_eventuallyEq (hF.mono fun t ht => ht x)
  · have hs : ∀ᶠ t in 𝓝 t₀, ‖H t - H t₀‖ ≤ 1 / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h.continuousAt).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
      exact this
    filter_upwards [hb, hF, hs] with t ht hFt hst x
    rw [← hN, hFt, hF.self_of_nhds, h0]
    have e : ‖H t x - x‖ ≤ ‖H t - H t₀‖ * ‖x‖ := by
      have := (H t - H t₀).le_opNorm x
      rw [_root_.sub_apply] at this
      simpa only [h0, one_apply_eq_self] using this
    have hw : 0 < 1 + ‖x‖ := by positivity
    have hm := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f)
      (C := 2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1)) (x := x) (y := H t x) (fun y _ => f.differentiableAt) (fun y hy => by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
          have h2 := norm_sub_norm_le x y
          rw [mem_closedBall_iff_norm'] at hy
          linarith
        calc _ ≤ ‖fderiv ℝ f y‖ * (2 * (1 + ‖y‖)) ^ (N + 1) := by gcongr
          _ = 2 ^ (N + 1) * ((1 + ‖y‖) ^ (N + 1) * ‖fderiv ℝ f y‖) := by rw [mul_pow]; ring
          _ ≤ _ := by gcongr; exact hf y)
      (Metric.mem_closedBall_self (by positivity)) (by
        rw [mem_closedBall_iff_norm]
        nlinarith [norm_nonneg x])
    have e2 : ‖H t x - x‖ ≤ K * |t - t₀| * (1 + ‖x‖) := e.trans (by gcongr; simp)
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1) * (K * |t - t₀| * (1 + ‖x‖))) := by
          refine mul_le_mul_of_nonneg_left (hm.trans ?_) (by positivity)
          gcongr
      _ = _ := by rw [pow_succ (1 + ‖x‖) N]; field_simp

omit [DecidableEq l] in
theorem hasL2DerivAt_dilation {B : ℝ → EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {B' : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {t₀ : ℝ} (h : HasDerivAt B B' t₀) (h0 : IsUnit (B t₀)) :
    HasL2DerivAt (fun t => dilation (B t)) (fun f => vectorFieldDeriv (Ring.inverse (B t₀) * B') (dilation (B t₀) f)) t₀ := fun f => by
  refine hasL2DerivAt_dilation_one (h.const_mul (Ring.inverse (B t₀))) (Ring.inverse_mul_cancel _ h0) _ ?_
  filter_upwards [h.continuousAt.eventually (Units.isOpen.mem_nhds h0)] with t ht x
  rw [dilation_apply ht, dilation_apply h0, ← mul_apply_eq_comp, ← mul_assoc, Ring.mul_inverse_cancel _ h0, one_mul]

omit [DecidableEq l] in
theorem hasL2DerivAt_bigCellOp {Ai B C : ℝ → EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {Ai' B' C' : EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, HasL2DerivAt (fun t => bigCellOp (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = quadMul C' f + vectorFieldDeriv Ai' f + fourierCLM ℂ (RealSchwartz l) (quadMul (-B') (fourierInvCLM ℂ (RealSchwartz l) f)) + (c' : ℂ) • f) := by
  have h1 := (hasL2DerivAt_chirp (hA.mul hB).neg).mul (HasL2DerivAt.const (fourierInvCLM ℂ (RealSchwartz l)) t₀) (.of_forall fun t => isL2Isometry_chirp _)
  have h2 := (HasL2DerivAt.const (fourierCLM ℂ (RealSchwartz l)) t₀).mul h1 (.of_forall fun t => isL2Isometry_fourierCLM)
  have h3 := ((hasL2DerivAt_dilation hA h.self_of_nhds.1).smul hc.ofReal_comp).mul h2 (h.mono fun t ht => isL2Isometry_dilation ht.1 ht.2)
  have h4 := (hasL2DerivAt_chirp (hC.mul hA)).mul h3 (.of_forall fun t => isL2Isometry_chirp _)
  refine ⟨_, h4, fun e1 e2 e3 e4 f => ?_⟩
  have e5 : fourierCLM ℂ (RealSchwartz l) (fourierInvCLM ℂ (RealSchwartz l) f) = f := by
    rw [← mul_apply_eq_comp, fourierCLM_mul_fourierInvCLM, one_apply_eq_self]
  simp [e1, e2, e3, e4, chirp_zero, dilation_one]
  abel

end Langlands.Theta.Real.Internal
