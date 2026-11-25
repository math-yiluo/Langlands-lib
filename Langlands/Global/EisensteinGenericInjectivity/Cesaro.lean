import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Algebra.Field.GeomSum

/-! # Extracting one coefficient of an absolutely convergent exponential series -/

noncomputable section

open Filter Topology Complex

namespace Langlands.Global.EisensteinGenericInjectivity

/-- Cesàro means of the powers of a unit complex number other than one tend to zero. -/
theorem tendsto_cesaro_pow_zero {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, z ^ m) atTop (𝓝 0) := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hb : ∀ M : ℕ, ‖∑ m ∈ Finset.range M, z ^ m‖ ≤ 2 / ‖z - 1‖ := by
    intro M
    rw [geom_sum_eq h1, norm_div]
    gcongr
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  have hinv : Tendsto (fun M : ℕ => ((M : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_)
    (by simpa using hinv.mul_const (2 / ‖z - 1‖))
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hb M) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The Cesàro means of the powers of a unit complex number are bounded by one. -/
theorem norm_cesaro_pow_le {z : ℂ} (hz : ‖z‖ = 1) (M : ℕ) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, z ^ m‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h : ‖∑ m ∈ Finset.range M, z ^ m‖ ≤ M := by
    calc ‖∑ m ∈ Finset.range M, z ^ m‖ ≤ ∑ m ∈ Finset.range M, ‖z ^ m‖ := norm_sum_le _ _
      _ = M := by simp [norm_pow, hz]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  calc (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M, z ^ m‖ ≤ (M : ℝ)⁻¹ * M :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hM'.le)
    _ = 1 := inv_mul_cancel₀ hM'.ne'

/-- If all power moments `∑ B c ζ_c ^ m` of an absolutely summable family vanish, the
coefficient at the unique index with `ζ = 1` vanishes. -/
theorem coeff_eq_zero_of_forall_pow_tsum_eq_zero {ι : Type*} {B ζ : ι → ℂ} {c₀ : ι}
    (hB : Summable fun c => ‖B c‖) (hζ : ∀ c, ‖ζ c‖ = 1) (hζ₀ : ζ c₀ = 1)
    (hζ₁ : ∀ c, c ≠ c₀ → ζ c ≠ 1) (h : ∀ m : ℕ, ∑' c, B c * ζ c ^ m = 0) : B c₀ = 0 := by
  classical
  let A : ℕ → ι → ℂ := fun M c => (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ζ c ^ m
  have hlim : Tendsto (fun M => ∑' c, B c * A M c) atTop
      (𝓝 (∑' c, if c = c₀ then B c₀ else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hB (fun c => ?_) (Eventually.of_forall
      fun M c => ?_)
    · by_cases hc : c = c₀
      · subst hc
        simp only [ite_true]
        have hA : ∀ M : ℕ, 1 ≤ M → B c * A M c = B c := by
          intro M hM
          simp only [A, hζ₀, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one]
          rw [inv_mul_cancel₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hM)), mul_one]
        exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun M hM => (hA M hM).symm⟩)
      · simp only [hc, ite_false]
        simpa using (tendsto_cesaro_pow_zero (hζ c) (hζ₁ c hc)).const_mul (B c)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_cesaro_pow_le (hζ c) M)
  have hzero : ∀ M, ∑' c, B c * A M c = 0 := by
    intro M
    have hs : ∀ m, Summable fun c => B c * ζ c ^ m := fun m =>
      Summable.of_norm_bounded hB fun c => by
        rw [norm_mul, norm_pow, hζ c, one_pow, mul_one]
    calc ∑' c, B c * A M c = (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∑' c, B c * ζ c ^ m := by
          rw [← Summable.tsum_finsetSum fun m _ => hs m, ← tsum_mul_left]
          congr 1
          funext c
          simp only [A, Finset.mul_sum]
          ring_nf
      _ = 0 := by simp [h]
  simp only [hzero, tsum_ite_eq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Choice of a frequency scale `τ` for which no other frequency differs from the
distinguished one by a multiple of `2π / τ`. -/
theorem exists_scale_ne_one {ι : Type*} [Countable ι] (θ : ι → ℝ) (c₀ : ι)
    (hθ : ∀ c, c ≠ c₀ → θ c ≠ θ c₀) :
    ∃ τ : ℝ, ∀ c, c ≠ c₀ → Complex.exp (I * ((τ * (θ c - θ c₀) : ℝ) : ℂ)) ≠ 1 := by
  let S : Set ℝ := ⋃ c : {c // c ≠ c₀},
    Set.range fun k : ℤ => 2 * Real.pi * k / (θ c - θ c₀)
  have hS : S.Countable := Set.countable_iUnion fun c => Set.countable_range _
  obtain ⟨τ, hτ⟩ := (hS.dense_compl ℝ).nonempty
  refine ⟨τ, fun c hc hexp => hτ ?_⟩
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  have hd : θ c - θ c₀ ≠ 0 := sub_ne_zero.mpr (hθ c hc)
  refine Set.mem_iUnion.mpr ⟨⟨c, hc⟩, k, ?_⟩
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add, Complex.intCast_re, Complex.intCast_im, mul_zero,
    sub_zero, Complex.mul_re, Complex.ofReal_mul, Complex.re_ofNat, Complex.im_ofNat] at him
  field_simp
  linarith

/-- **Coefficient extraction.** Let `B` be an absolutely summable family on a countable index
type and `θ` real frequencies such that `c₀` is the only index of frequency `θ c₀`. If
`B c₀ ≠ 0`, then for some real `τ` and some natural number `m` the imaginary shift
`∑ B c exp(i m τ θ c)` is nonzero. -/
theorem exists_shift_tsum_ne_zero {ι : Type*} [Countable ι] {B : ι → ℂ} {θ : ι → ℝ} {c₀ : ι}
    (hB : Summable fun c => ‖B c‖) (hθ : ∀ c, c ≠ c₀ → θ c ≠ θ c₀) (h₀ : B c₀ ≠ 0) :
    ∃ τ : ℝ, ∃ m : ℕ, ∑' c, B c * Complex.exp (I * (((m : ℝ) * τ * θ c : ℝ) : ℂ)) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_scale_ne_one θ c₀ hθ
  refine ⟨τ, ?_⟩
  by_contra! hall
  let ζ : ι → ℂ := fun c => Complex.exp (I * ((τ * (θ c - θ c₀) : ℝ) : ℂ))
  let w : ℂ := Complex.exp (I * ((τ * θ c₀ : ℝ) : ℂ))
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hnorm : ∀ c, ‖ζ c‖ = 1 := fun c => by
    simp only [ζ, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_self, Real.exp_zero]
  have hsplit : ∀ (m : ℕ) (c : ι), Complex.exp (I * (((m : ℝ) * τ * θ c : ℝ) : ℂ)) =
      w ^ m * ζ c ^ m := by
    intro m c
    rw [← mul_pow, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine h₀ (coeff_eq_zero_of_forall_pow_tsum_eq_zero hB hnorm ?_ (fun c hc => hτ c hc)
    fun m => ?_)
  · simp [ζ]
  · have h := hall m
    simp_rw [hsplit, mul_left_comm (B _), tsum_mul_left] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw)

end Langlands.Global.EisensteinGenericInjectivity
