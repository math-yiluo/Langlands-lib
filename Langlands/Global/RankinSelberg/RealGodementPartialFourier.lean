import Langlands.Global.RankinSelberg.RealGodementScaledFourier

/-! # Rapid decay of the partial real Schwartz Fourier integral -/

noncomputable section

open Langlands.LocalFactor.Archimedean MeasureTheory Filter
open scoped ENNReal SchwartzMap RealInnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u v

private theorem exists_weighted_majorant {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [MeasurableSpace W]
    (μ : Measure W) [μ.HasTemperateGrowth] (Φ : 𝓢(V, ℂ)) (N : ℕ) :
    ∃ B : W → ℝ, Integrable B μ ∧ (∀ x, 0 ≤ B x) ∧
      ∀ (z : V) (x : W) (r : ℝ), 0 ≤ r → r ≤ ‖z‖ → ‖x‖ ≤ ‖z‖ →
        (1 + r) ^ N * ‖Φ z‖ ≤ B x := by
  let l := μ.integrablePower
  let d := N + l
  let C := (2 : ℝ) ^ d * (SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ d 0 Φ)
  refine ⟨fun x => C * (1 + ‖x‖) ^ (-(l : ℝ)),
    (μ.integrable_pow_neg_integrablePower).const_mul _, fun x => by positivity, ?_⟩
  intro z x r hr hrz hxz
  have hDecay : ‖Φ z‖ ≤ C * (1 + ‖z‖) ^ (-(d : ℝ)) := by
    simpa only [pow_zero, one_mul, C] using
      (pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := d) (norm_nonneg z) (norm_nonneg (Φ z))
        (Φ.norm_le_seminorm ℝ z) (by simpa only [zero_add] using Φ.norm_pow_mul_le_seminorm ℝ d z))
  have hWeight : (1 + r) ^ N * (1 + ‖x‖) ^ l ≤ (1 + ‖z‖) ^ d := by
    rw [show d = N + l from rfl, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hrz) _)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hxz) _) (by positivity) (by positivity)
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖z‖), Real.rpow_natCast, ← div_eq_mul_inv] at hDecay
  change (1 + r) ^ N * ‖Φ z‖ ≤ C * (1 + ‖x‖) ^ (-(l : ℝ))
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ((1 + r) ^ N * (1 + ‖x‖) ^ l) * ‖Φ z‖ := by ring
    _ ≤ (1 + ‖z‖) ^ d * ‖Φ z‖ := mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
    _ ≤ C := by
      rw [mul_comm]
      exact (le_div_iff₀ (by positivity)).mp hDecay

private theorem norm_integral_weighted_slice {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [MeasurableSpace W]
    (μ : Measure W) [μ.HasTemperateGrowth] (Φ : 𝓢(V, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : W → V) (χ : W → Circle) (r : ℝ), 0 ≤ r →
      (∀ x, r ≤ ‖z x‖) → (∀ x, ‖x‖ ≤ ‖z x‖) →
      (1 + r) ^ N * ‖∫ x, χ x • Φ (z x) ∂μ‖ ≤ C := by
  obtain ⟨B, hB, hB0, hBounds⟩ := exists_weighted_majorant μ Φ N
  refine ⟨∫ x, B x ∂μ, integral_nonneg hB0, ?_⟩
  intro z χ r hr hrz hxz
  have hP : 0 ≤ (1 + r) ^ N := by positivity
  calc
    _ = ‖∫ x, ((1 + r) ^ N : ℝ) • (χ x • Φ (z x)) ∂μ‖ := by
      rw [integral_smul, norm_smul, Real.norm_of_nonneg hP]
    _ ≤ _ := norm_integral_le_of_norm_le hB (Eventually.of_forall fun x => by
      simpa only [norm_smul, Real.norm_of_nonneg hP, Circle.smul_def, smul_eq_mul, norm_mul,
        Circle.norm_coe, one_mul] using hBounds (z x) x r hr (hrz x) (hxz x))

private theorem selfDual_hasTemperateGrowth {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (a : ℝˣ) :
    (euclideanSelfDualMeasure a V).HasTemperateGrowth :=
  ⟨⟨(volume : Measure V).integrablePower,
    ((volume : Measure V).integrable_pow_neg_integrablePower).smul_measure ENNReal.ofReal_ne_top⟩⟩

section Product

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

local notation "P" => WithLp 2 (E × F)

/-- The partial positive Fourier transform using the specified real self-dual measure. -/
def scaledFirstFactorFourier (a : ℝˣ) (Φ : 𝓢(P, ℂ)) (ξ : E) (η : F) : ℂ :=
  ∫ x : E, realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η))
    ∂euclideanSelfDualMeasure a E

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
private theorem continuous_scaledFirstFactorFourier (a : ℝˣ) (Φ : 𝓢(P, ℂ)) :
    Continuous (fun p : E × F => scaledFirstFactorFourier a Φ p.1 p.2) := by
  let μ := euclideanSelfDualMeasure a E
  let : μ.HasTemperateGrowth := selfDual_hasTemperateGrowth a
  obtain ⟨B, hB, _, hBounds⟩ := exists_weighted_majorant μ Φ 0
  let f : (E × F) × E → ℂ := fun p =>
    realScaledCharacter a (inner ℝ p.2 p.1.1) • Φ (WithLp.toLp 2 (p.2, p.1.2))
  have hf : Continuous f := by
    exact ((realScaledCharacter a).continuous_toFun.comp
      (continuous_snd.inner (𝕜 := ℝ) continuous_fst.fst)).smul
        (Φ.continuous.comp ((WithLp.prod_continuous_toLp 2 E F).comp
          (continuous_snd.prodMk continuous_fst.snd)))
  change Continuous (fun p : E × F => ∫ x, f (p, x) ∂μ)
  refine continuous_of_dominated (bound := B)
    (fun p => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) ?_ hB ?_
  · intro p
    refine Eventually.of_forall fun x => ?_
    have h := hBounds (WithLp.toLp 2 (x, p.2)) x 0 le_rfl (norm_nonneg _)
      (WithLp.norm_fst_le (α := E) (β := F) (WithLp.toLp 2 (x, p.2)))
    simpa only [f, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe,
      one_mul, pow_zero] using h
  · exact Eventually.of_forall fun x => hf.comp (continuous_id.prodMk continuous_const)

private theorem scaledFirstFactorFourier_decay (a : ℝˣ) (Φ : 𝓢(P, ℂ)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : E) (η : F),
      (1 + ‖ξ‖) ^ N * (1 + ‖η‖) ^ N * ‖scaledFirstFactorFourier a Φ ξ η‖ ≤ C := by
  let μ := euclideanSelfDualMeasure a E
  let ν := euclideanSelfDualMeasure a F
  let : μ.HasTemperateGrowth := selfDual_hasTemperateGrowth a
  let : ν.HasTemperateGrowth := selfDual_hasTemperateGrowth a
  obtain ⟨C₁, hC₁, h₁⟩ := norm_integral_weighted_slice μ Φ (N + N)
  obtain ⟨C₂, hC₂, h₂⟩ := norm_integral_weighted_slice ν (scaledEuclideanFourier a Φ) (N + N)
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun ξ η => ?_⟩
  have hy : (1 + ‖η‖) ^ (N + N) * ‖scaledFirstFactorFourier a Φ ξ η‖ ≤ C₁ :=
    h₁ (fun x => WithLp.toLp 2 (x, η)) (fun x => realScaledCharacter a (inner ℝ x ξ))
      ‖η‖ (norm_nonneg _) (fun x => WithLp.norm_snd_le (α := E) (β := F) (WithLp.toLp 2 (x, η)))
      (fun x => WithLp.norm_fst_le (α := E) (β := F) (WithLp.toLp 2 (x, η)))
  have hx : (1 + ‖ξ‖) ^ (N + N) * ‖scaledFirstFactorFourier a Φ ξ η‖ ≤ C₂ := by
    unfold scaledFirstFactorFourier
    rw [← (realGodementScaledProductFourier E F a Φ ξ η).2.2]
    exact h₂ (fun y => WithLp.toLp 2 (ξ, y)) (fun y => realScaledCharacter a (-(inner ℝ y η)))
      ‖ξ‖ (norm_nonneg _) (fun y => WithLp.norm_fst_le (α := E) (β := F) (WithLp.toLp 2 (ξ, y)))
      (fun y => WithLp.norm_snd_le (α := E) (β := F) (WithLp.toLp 2 (ξ, y)))
  rcases le_total ‖ξ‖ ‖η‖ with h | h
  · calc
      _ ≤ (1 + ‖η‖) ^ (N + N) * ‖scaledFirstFactorFourier a Φ ξ η‖ := by
        rw [pow_add]
        gcongr
      _ ≤ C₁ := hy
      _ ≤ C₁ + C₂ := le_add_of_nonneg_right hC₂
  · calc
      _ ≤ (1 + ‖ξ‖) ^ (N + N) * ‖scaledFirstFactorFourier a Φ ξ η‖ := by
        rw [pow_add]
        gcongr
      _ ≤ C₂ := hx
      _ ≤ C₁ + C₂ := le_add_of_nonneg_left hC₁

end Product

/-- The partial transform is continuous and has simultaneous decay of every
order in the frequency and the untouched coordinate. -/
def RealGodementPartialFourierStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (a : ℝˣ) (Φ : 𝓢(WithLp 2 (E × F), ℂ)),
    Continuous (fun p : E × F => scaledFirstFactorFourier a Φ p.1 p.2) ∧
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : E) (η : F),
      (1 + ‖ξ‖) ^ N * (1 + ‖η‖) ^ N * ‖scaledFirstFactorFourier a Φ ξ η‖ ≤ C

theorem realGodementPartialFourier : RealGodementPartialFourierStatement.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ a Φ
  exact ⟨continuous_scaledFirstFactorFourier a Φ, scaledFirstFactorFourier_decay a Φ⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
