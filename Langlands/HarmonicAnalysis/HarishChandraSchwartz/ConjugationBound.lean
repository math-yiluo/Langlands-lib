import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds

/-! # The estimate away from `a⁻¹ Γ a M Γ̄` in the proof of Proposition VIII.3.1

Waldspurger 2003, proof of Proposition VIII.3.1, inequality (3): for `f₁, f₂ ∈ C(G)` and
`r ∈ ℝ` there is `C₃` with `∫_{S(a)} |f₁(a g a⁻¹) f₂(g)| dg ≤ C₃ δ₀(a) (1 + σ(a))^{-r}` for
the relevant `a`, where on `S(a)` one has (2): `1 + σ(a) ≤ C₂ (1 + σ(g) + σ(a g a⁻¹))`.
The proof bounds `f₁` and `f₂` by `Ξ`, replaces `g` by `h g k` (`h, k ∈ K`), integrates
over `K × K` with Lemmas II.1.3 and II.1.4, and ends with Lemmas II.1.5 and II.1.1.

Here the weights satisfy the hypotheses `ConvolutionWeights` of `Convolution` (which
contain Lemmas II.1.3, II.1.4 and II.1.5), the Haar measure is left and right invariant,
`σ` is right `K`-invariant, inequality (2) and the upper bound of Lemma II.1.1 are
hypotheses, and `a` ranges over an arbitrary set `T`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

/-- If `t ≤ C (1 + x + y)` with `x, y ≥ 0`, `t, C > 0`, then
`(1 + x)^{-r} (1 + y)^{-r} ≤ C^r t^{-r}` for `r ≥ 0`. -/
theorem one_add_rpow_neg_mul_le {x y t C r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t)
    (hC : 0 < C) (hr : 0 ≤ r) (h : t ≤ C * (1 + x + y)) :
    (1 + x) ^ (-r) * (1 + y) ^ (-r) ≤ C ^ r * t ^ (-r) := by
  have h1 : t / C ≤ (1 + x) * (1 + y) := by
    rw [div_le_iff₀ hC]
    nlinarith [mul_nonneg (mul_nonneg hC.le hx) hy]
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  calc ((1 + x) * (1 + y)) ^ (-r) ≤ (t / C) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (div_pos ht hC) h1 (by linarith)
    _ = C ^ r * t ^ (-r) := by
        rw [Real.div_rpow ht.le hC.le, Real.rpow_neg hC.le, div_eq_mul_inv, inv_inv, mul_comm]

/-- Inequality (2) of the proof of Proposition VIII.3.1: there is `C₂` with
`1 + σ(a) ≤ C₂ (1 + σ(g) + σ(a g a⁻¹))` for `a ∈ T` and `g ∈ S(a)`. For Waldspurger's data
`T = Ā⁺₀(α) ∩ G¹` and `S(a) = G - a⁻¹ Γ a M Γ̄`, and (2) follows from Lemma II.3.5 and
inequality (1) of the proof. -/
def ConjugationSigmaBound {G : Type*} [Group G] (σ : G → ℝ) (T : Set G) (S : G → Set G) :
    Prop :=
  ∃ C₂ : ℝ, ∀ a ∈ T, ∀ g ∈ S a, 1 + σ a ≤ C₂ * (1 + σ g + σ (a * g * a⁻¹))

section Averaging

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}

namespace ConvolutionWeights

omit [SecondCountableTopology G] in
/-- `Ξ` is right `K`-invariant (from left invariance and Lemma II.1.4). -/
theorem xi_mul_right (hw : ConvolutionWeights μ K Ξ σ) {k : G} (hk : k ∈ K) (g : G) :
    Ξ (g * k) = Ξ g := by
  rw [← hw.xi_inv, mul_inv_rev, hw.xi_mul_left _ (K.inv_mem hk), hw.xi_inv]

variable [SFinite μ]

/-- Lemma II.1.3 after averaging a left translation over `K`: for `W` measurable and
left `K`-invariant, `∫_G Ξ(x g y) W(g) dg = Ξ(x) ∫_G Ξ(g y) W(g) dg`. -/
theorem lintegral_xi_mul_left [μ.IsMulLeftInvariant] (hw : ConvolutionWeights μ K Ξ σ)
    {W : G → ℝ≥0∞} (hWm : Measurable W) (hWK : ∀ k ∈ K, ∀ g, W (k * g) = W g) (x y : G) :
    ∫⁻ g, ENNReal.ofReal (Ξ (x * g * y)) * W g ∂μ =
      ENNReal.ofReal (Ξ x) * ∫⁻ g, ENNReal.ofReal (Ξ (g * y)) * W g ∂μ := by
  set ν := normalizedHaar K
  set F : G → ℝ≥0∞ := fun g => ENNReal.ofReal (Ξ (x * g * y)) * W g with hF
  have htrans : ∀ k : K, ∫⁻ g, F g ∂μ =
      ∫⁻ g, ENNReal.ofReal (Ξ (x * k * (g * y))) * W g ∂μ := by
    intro k
    rw [← lintegral_mul_left_eq_self F (k : G)]
    refine lintegral_congr fun g => ?_
    simp only [hF]
    rw [hWK _ k.2, show x * ((k : G) * g) * y = x * k * (g * y) by group]
  have havg : ∫⁻ g, F g ∂μ =
      ∫⁻ k : K, ∫⁻ g, ENNReal.ofReal (Ξ (x * k * (g * y))) * W g ∂μ ∂ν := by
    simp_rw [← htrans]
    rw [lintegral_const, measure_univ, mul_one]
  have hmeas : AEMeasurable (Function.uncurry fun (k : K) (g : G) =>
      ENNReal.ofReal (Ξ (x * k * (g * y))) * W g) (ν.prod μ) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : K × G => ENNReal.ofReal (Ξ (x * p.1 * (p.2 * y))) * W p.2
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_))
      (hWm.comp measurable_snd)
    exact hw.continuous_xi.comp ((continuous_const.mul
      (continuous_subtype_val.comp continuous_fst)).mul (continuous_snd.mul continuous_const))
  rw [havg, lintegral_lintegral_swap hmeas]
  have hinner : ∀ g : G, ∫⁻ k : K, ENNReal.ofReal (Ξ (x * k * (g * y))) * W g ∂ν =
      ENNReal.ofReal (Ξ x) * (ENNReal.ofReal (Ξ (g * y)) * W g) := by
    intro g
    have hc : Continuous fun k : K => Ξ (x * k * (g * y)) :=
      hw.continuous_xi.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hint : Integrable (fun k : K => Ξ (x * k * (g * y))) ν :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [lintegral_mul_const _ hc.measurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun k => (hw.pos _).le), hw.integral_xi,
      ENNReal.ofReal_mul (hw.pos x).le, mul_assoc]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Lemma II.1.3 after averaging a right translation over `K`: for `W` measurable and
right `K`-invariant, `∫_G Ξ(g y) W(g) dg = Ξ(y) ∫_G Ξ(g) W(g) dg`. -/
theorem lintegral_xi_mul_right [μ.IsMulRightInvariant] (hw : ConvolutionWeights μ K Ξ σ)
    {W : G → ℝ≥0∞} (hWm : Measurable W) (hWK : ∀ k ∈ K, ∀ g, W (g * k) = W g) (y : G) :
    ∫⁻ g, ENNReal.ofReal (Ξ (g * y)) * W g ∂μ =
      ENNReal.ofReal (Ξ y) * ∫⁻ g, ENNReal.ofReal (Ξ g) * W g ∂μ := by
  set ν := normalizedHaar K
  set F : G → ℝ≥0∞ := fun g => ENNReal.ofReal (Ξ (g * y)) * W g with hF
  have htrans : ∀ k : K, ∫⁻ g, F g ∂μ =
      ∫⁻ g, ENNReal.ofReal (Ξ (g * k * y)) * W g ∂μ := by
    intro k
    rw [← lintegral_mul_right_eq_self F (k : G)]
    refine lintegral_congr fun g => ?_
    simp only [hF]
    rw [hWK _ k.2]
  have havg : ∫⁻ g, F g ∂μ =
      ∫⁻ k : K, ∫⁻ g, ENNReal.ofReal (Ξ (g * k * y)) * W g ∂μ ∂ν := by
    simp_rw [← htrans]
    rw [lintegral_const, measure_univ, mul_one]
  have hmeas : AEMeasurable (Function.uncurry fun (k : K) (g : G) =>
      ENNReal.ofReal (Ξ (g * k * y)) * W g) (ν.prod μ) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : K × G => ENNReal.ofReal (Ξ (p.2 * p.1 * y)) * W p.2
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_))
      (hWm.comp measurable_snd)
    exact hw.continuous_xi.comp ((continuous_snd.mul
      (continuous_subtype_val.comp continuous_fst)).mul continuous_const)
  rw [havg, lintegral_lintegral_swap hmeas]
  have hinner : ∀ g : G, ∫⁻ k : K, ENNReal.ofReal (Ξ (g * k * y)) * W g ∂ν =
      ENNReal.ofReal (Ξ y) * (ENNReal.ofReal (Ξ g) * W g) := by
    intro g
    have hc : Continuous fun k : K => Ξ (g * k * y) :=
      hw.continuous_xi.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hint : Integrable (fun k : K => Ξ (g * k * y)) ν :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [lintegral_mul_const _ hc.measurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun k => (hw.pos _).le), hw.integral_xi,
      ENNReal.ofReal_mul (hw.pos g).le]
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The `K × K`-averaging step of the proof of Proposition VIII.3.1: for `W` measurable
and bi-invariant under `K`, `∫_G Ξ(x g y) W(g) dg = Ξ(x) Ξ(y) ∫_G Ξ(g) W(g) dg`. -/
theorem lintegral_xi_mul_mul [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (hw : ConvolutionWeights μ K Ξ σ) {W : G → ℝ≥0∞} (hWm : Measurable W)
    (hWl : ∀ k ∈ K, ∀ g, W (k * g) = W g) (hWr : ∀ k ∈ K, ∀ g, W (g * k) = W g)
    (x y : G) :
    ∫⁻ g, ENNReal.ofReal (Ξ (x * g * y)) * W g ∂μ =
      ENNReal.ofReal (Ξ x) * ENNReal.ofReal (Ξ y) * ∫⁻ g, ENNReal.ofReal (Ξ g) * W g ∂μ := by
  rw [hw.lintegral_xi_mul_left hWm hWl, hw.lintegral_xi_mul_right hWm hWr, mul_assoc]

/-- Proposition VIII.3.1, inequality (3), for arbitrary sets `T` and `S(a)`: if
`1 + σ(a) ≤ C₂ (1 + σ(g) + σ(a g a⁻¹))` for `a ∈ T` and `g ∈ S(a)` (inequality (2)), and
`Ξ(a) ≤ C e(a) (1 + σ(a))^d` on `T` (the upper bound of Lemma II.1.1), then for
`f₁, f₂` with all `ν_r` finite and every `r` there is `c` with
`∫_{S(a)} |f₁(a g a⁻¹)| |f₂(g)| dg ≤ c e(a)² (1 + σ(a))^{-r}` for all `a ∈ T`. -/
theorem lintegral_conj_mul_le [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (hw : ConvolutionWeights μ K Ξ σ) (hσK : ∀ k ∈ K, ∀ g, σ (g * k) = σ g)
    {T : Set G} {S : G → Set G} {e : G → ℝ} (hup : XiUpperBound Ξ σ T e)
    (h2 : ConjugationSigmaBound σ T S)
    {f₁ f₂ : G → ℂ} (hf₁ : ∀ r, nu Ξ σ r f₁ < ⊤) (hf₂ : ∀ r, nu Ξ σ r f₂ < ⊤) (r : ℝ) :
    ∃ c : ℝ≥0, ∀ a ∈ T, ∫⁻ g in S a, ‖f₁ (a * g * a⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) := by
  obtain ⟨C, d, hup⟩ := hup
  obtain ⟨C₂, h2⟩ := h2
  obtain ⟨d₀, hsq⟩ := hw.square
  set C₂' := max C₂ 1 with hC₂'_def
  have hC₂' : 0 < C₂' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r' := max (r + 2 * d) 0 with hr'_def
  have hr' : 0 ≤ r' := le_max_right _ _
  have hrr' : r + 2 * d ≤ r' := le_max_left _ _
  set r'' : ℝ := (d₀ : ℝ) with hr''_def
  have hr'' : 0 ≤ r'' := Nat.cast_nonneg _
  have hpos : ∀ g, 0 < 1 + σ g := fun g => by linarith [hw.nonneg g]
  set W : G → ℝ≥0∞ := fun g => ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r'')) with hW_def
  have hσc : Continuous fun g => (1 + σ g) ^ (-r'') :=
    (continuous_const.add hw.continuous_sigma).rpow_const fun g => Or.inl (hpos g).ne'
  have hWm : Measurable W :=
    ENNReal.measurable_ofReal.comp (hw.continuous_xi.mul hσc).measurable
  have hWl : ∀ k ∈ K, ∀ g, W (k * g) = W g := fun k hk g => by
    simp only [hW_def, hw.xi_mul_left k hk, hw.sigma_mul_left k hk]
  have hWr : ∀ k ∈ K, ∀ g, W (g * k) = W g := fun k hk g => by
    simp only [hW_def, hw.xi_mul_right hk, hσK k hk]
  set I : ℝ≥0∞ := ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-r'')) ∂μ with hI_def
  have hI : I ≠ ⊤ := hsq.ne
  have hIW : ∫⁻ g, ENNReal.ofReal (Ξ g) * W g ∂μ = I := by
    refine lintegral_congr fun g => ?_
    simp only [hW_def]
    rw [← ENNReal.ofReal_mul (hw.pos g).le]
    congr 1
    ring
  set c₀ : ℝ≥0∞ := nu Ξ σ r' f₁ * nu Ξ σ (r' + r'') f₂ with hc₀_def
  have hc₀ : c₀ ≠ ⊤ := ENNReal.mul_ne_top (hf₁ r').ne (hf₂ (r' + r'')).ne
  set B : ℝ := C₂' ^ r' * C ^ 2 with hB_def
  have hB : 0 ≤ B := by positivity
  refine ⟨(c₀ * ENNReal.ofReal B * I).toNNReal, fun a ha => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc₀ ENNReal.ofReal_ne_top) hI)]
  set A : ℝ := C₂' ^ r' * (1 + σ a) ^ (-r') with hA_def
  have hA : 0 ≤ A := by
    have := hpos a
    positivity
  -- pointwise bound on `S(a)`, from inequality (2)
  have hpt : ∀ g ∈ S a, ‖f₁ (a * g * a⁻¹)‖ₑ * ‖f₂ g‖ₑ ≤
      c₀ * ENNReal.ofReal A * (ENNReal.ofReal (Ξ (a * g * a⁻¹)) * W g) := by
    intro g hg
    set x := a * g * a⁻¹
    have hkey : (1 + σ g) ^ (-r') * (1 + σ x) ^ (-r') ≤ C₂' ^ r' * (1 + σ a) ^ (-r') := by
      refine one_add_rpow_neg_mul_le (hw.nonneg g) (hw.nonneg x) (hpos a) hC₂' hr' ?_
      calc 1 + σ a ≤ C₂ * (1 + σ g + σ x) := h2 a ha g hg
        _ ≤ C₂' * (1 + σ g + σ x) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hw.nonneg g, hw.nonneg x])
    have hsplit : (1 + σ g) ^ (-(r' + r'')) = (1 + σ g) ^ (-r') * (1 + σ g) ^ (-r'') := by
      rw [neg_add, Real.rpow_add (hpos g)]
    have hD : 0 ≤ Ξ x * (Ξ g * (1 + σ g) ^ (-r'')) := by
      have := (hw.pos x).le
      have := (hw.pos g).le
      have := (hpos g).le
      positivity
    have hreal : Ξ x * (1 + σ x) ^ (-r') * (Ξ g * (1 + σ g) ^ (-(r' + r''))) ≤
        A * (Ξ x * (Ξ g * (1 + σ g) ^ (-r''))) := by
      rw [hsplit]
      calc Ξ x * (1 + σ x) ^ (-r') * (Ξ g * ((1 + σ g) ^ (-r') * (1 + σ g) ^ (-r'')))
          = (Ξ x * (Ξ g * (1 + σ g) ^ (-r''))) * ((1 + σ g) ^ (-r') * (1 + σ x) ^ (-r')) := by
            ring
        _ ≤ (Ξ x * (Ξ g * (1 + σ g) ^ (-r''))) * (C₂' ^ r' * (1 + σ a) ^ (-r')) :=
            mul_le_mul_of_nonneg_left hkey hD
        _ = A * (Ξ x * (Ξ g * (1 + σ g) ^ (-r''))) := by rw [hA_def]; ring
    have hx0 : 0 ≤ Ξ x * (1 + σ x) ^ (-r') :=
      mul_nonneg (hw.pos x).le (Real.rpow_nonneg (hpos x).le _)
    calc ‖f₁ x‖ₑ * ‖f₂ g‖ₑ
        ≤ (nu Ξ σ r' f₁ * ENNReal.ofReal (Ξ x * (1 + σ x) ^ (-r'))) *
            (nu Ξ σ (r' + r'') f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-(r' + r'')))) :=
          mul_le_mul' (enorm_le_nu_mul hw.pos hw.nonneg f₁ r' x)
            (enorm_le_nu_mul hw.pos hw.nonneg f₂ (r' + r'') g)
      _ = c₀ * ENNReal.ofReal (Ξ x * (1 + σ x) ^ (-r') *
            (Ξ g * (1 + σ g) ^ (-(r' + r'')))) := by
          rw [ENNReal.ofReal_mul hx0, hc₀_def]
          ring
      _ ≤ c₀ * ENNReal.ofReal (A * (Ξ x * (Ξ g * (1 + σ g) ^ (-r'')))) := by
          gcongr
      _ = c₀ * ENNReal.ofReal A * (ENNReal.ofReal (Ξ x) * W g) := by
          rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (hw.pos x).le, hW_def]
          ring
  have hRm : Measurable fun g => c₀ * ENNReal.ofReal A *
      (ENNReal.ofReal (Ξ (a * g * a⁻¹)) * W g) := by
    refine Measurable.const_mul (Measurable.mul ?_ hWm) _
    exact ENNReal.measurable_ofReal.comp
      (hw.continuous_xi.comp ((continuous_const.mul continuous_id).mul continuous_const)).measurable
  -- the final real inequality, from the upper bound of Lemma II.1.1 at `a`
  have hfin : A * Ξ a ^ 2 ≤ B * (e a ^ 2 * (1 + σ a) ^ (-r)) := by
    have h1 : Ξ a ^ 2 ≤ (C * e a * (1 + σ a) ^ d) ^ 2 :=
      pow_le_pow_left₀ (hw.pos a).le (hup a ha) 2
    have h2' : ((1 + σ a) ^ d) ^ 2 = (1 + σ a) ^ (2 * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos a).le]
      ring_nf
    have h3 : (1 + σ a) ^ (-r') * (1 + σ a) ^ (2 * d) ≤ (1 + σ a) ^ (-r) := by
      rw [← Real.rpow_add (hpos a)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [hw.nonneg a]) (by linarith)
    have hC2 : 0 ≤ C₂' ^ r' := Real.rpow_nonneg hC₂'.le _
    calc A * Ξ a ^ 2 ≤ A * (C * e a * (1 + σ a) ^ d) ^ 2 := mul_le_mul_of_nonneg_left h1 hA
      _ = C₂' ^ r' * C ^ 2 * e a ^ 2 * ((1 + σ a) ^ (-r') * ((1 + σ a) ^ d) ^ 2) := by
          rw [hA_def]
          ring
      _ = C₂' ^ r' * C ^ 2 * e a ^ 2 * ((1 + σ a) ^ (-r') * (1 + σ a) ^ (2 * d)) := by
          rw [h2']
      _ ≤ C₂' ^ r' * C ^ 2 * e a ^ 2 * (1 + σ a) ^ (-r) := by
          have : 0 ≤ C₂' ^ r' * C ^ 2 * e a ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left h3 this
      _ = B * (e a ^ 2 * (1 + σ a) ^ (-r)) := by rw [hB_def]; ring
  calc ∫⁻ g in S a, ‖f₁ (a * g * a⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂μ
      ≤ ∫⁻ g in S a, c₀ * ENNReal.ofReal A * (ENNReal.ofReal (Ξ (a * g * a⁻¹)) * W g) ∂μ :=
        setLIntegral_mono hRm hpt
    _ ≤ ∫⁻ g, c₀ * ENNReal.ofReal A * (ENNReal.ofReal (Ξ (a * g * a⁻¹)) * W g) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = c₀ * ENNReal.ofReal A * ∫⁻ g, ENNReal.ofReal (Ξ (a * g * a⁻¹)) * W g ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc₀ ENNReal.ofReal_ne_top)
    _ = c₀ * I * ENNReal.ofReal (A * Ξ a ^ 2) := by
        rw [hw.lintegral_xi_mul_mul hWm hWl hWr, hw.xi_inv, hIW,
          ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (hw.pos a).le, ← sq]
        ring
    _ ≤ c₀ * I * ENNReal.ofReal (B * (e a ^ 2 * (1 + σ a) ^ (-r))) := by
        gcongr
    _ = c₀ * ENNReal.ofReal B * I * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r)) := by
        rw [ENNReal.ofReal_mul hB]
        ring

end ConvolutionWeights

end Averaging

end Langlands.HarishChandraSchwartz
