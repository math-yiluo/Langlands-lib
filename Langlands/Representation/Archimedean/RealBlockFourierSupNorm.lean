import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

/-! # Compact bounds for square-summable real block multipliers -/

noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealBlockFourierSupNorm

open RealBlockRotation RealBlockFourierFinite RealBlockFrobeniusMap RealBlockMultiplier
open Langlands.LocalFactor.Archimedean

private theorem factor_two_pi_pos : 0 < 2 * Real.pi := by positivity

private theorem coeff_normalize (f : ℝ → ℂ) (j : ℤ) :
    (2 * (Real.pi : ℂ))⁻¹ * coeff j f =
      fourierCoeffOn factor_two_pi_pos f j := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have : Fact (0 < 2 * Real.pi - 0) := ⟨by simpa using factor_two_pi_pos⟩
  rw [fourierCoeffOn_eq_integral, coeff]
  simp only [sub_zero, one_div, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [fourier_coe_apply]
  rw [mul_comm (f t)]
  congr 1
  · congr 1
    push_cast
    field_simp [hπ]
    ring

private theorem sum_norm_sq_blockFourierCoefficient_le {n p : ℕ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) (s : Finset ℤ)
    {A : ℝ} (hA : ∀ k ∈ unitaryCompact ℝ n, ‖f k‖ ≤ A) :
    ∑ j ∈ s, ‖(2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient n p j f g‖ ^ 2 ≤ A ^ 2 := by
  let F (θ : ℝ) := f (blockRotation n p θ * g)
  have hFc : Continuous F := hf.comp ((continuous_blockRotation n p).mul continuous_const)
  have hFa (θ : ℝ) : ‖F θ‖ ≤ A :=
    hA _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hg)
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hFp : MemLp F 2 (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    MemLp.of_bound hFc.aestronglyMeasurable A (Filter.Eventually.of_forall hFa)
  have hSum := hasSum_sq_fourierCoeffOn factor_two_pi_pos hFp
  have hInt : (∫ t in (0 : ℝ)..2 * Real.pi, ‖F t‖ ^ 2) ≤ (2 * Real.pi) * A ^ 2 := by
    have hv := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 2 * Real.pi) (f := fun t => ‖F t‖ ^ 2) (C := A ^ 2)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFa t) _)
    rw [sub_zero, abs_of_pos factor_two_pi_pos, mul_comm (A ^ 2)] at hv
    exact (le_abs_self _).trans hv
  simp_rw [blockFourierCoefficient_eq_coeff, coeff_normalize]
  calc
    _ ≤ _ := hSum.summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
    _ = (2 * Real.pi)⁻¹ * (∫ t in (0 : ℝ)..2 * Real.pi, ‖F t‖ ^ 2) := by
      simpa only [sub_zero, smul_eq_mul] using hSum.tsum_eq
    _ ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * A ^ 2) :=
      mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr factor_two_pi_pos.le)
    _ = A ^ 2 := inv_mul_cancel_left₀ factor_two_pi_pos.ne' _

/-- A square-summable block Fourier multiplier is bounded in the compact sup norm. -/
theorem norm_blockFrobMap_le {n p : ℕ} {ds es : List RealBlock} {ε : ℤ} {σ : ℂ}
    {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ) (hμ : Summable fun j => ‖μ j‖ ^ 2)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n)
    {A : ℝ} (hA : ∀ k ∈ unitaryCompact ℝ n, ‖f.val k‖ ≤ A) :
    ‖(blockFrobMap h f).val g‖ ≤ Real.sqrt (∑' j, ‖μ j‖ ^ 2) * A := by
  classical
  let c : ℂ := (2 * (Real.pi : ℂ))⁻¹
  let v (j : ℤ) := blockFourierCoefficient n p j f.val g
  have hf := f.property.1.1.1.continuous
  have hfinite := finite_support_blockFourierCoefficient h.lt hf f.property.2 hg
  let s := hfinite.toFinset
  have hs : Function.support (fun j => μ j * v j) ⊆ ↑s := by
    intro j hj
    rw [Set.Finite.coe_toFinset]
    exact fun hz => hj (mul_eq_zero.mpr (Or.inr hz))
  have hv := sum_norm_sq_blockFourierCoefficient_le (p := p) hf hg s hA
  have hA₀ := (norm_nonneg _).trans (hA g hg)
  rw [blockFrobMap_apply_of_mem h f hg, finsum_eq_sum_of_support_subset _ hs]
  change ‖c * (∑ j ∈ s, μ j * v j)‖ ≤ _
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm c]
  calc
    _ ≤ ∑ j ∈ s, ‖μ j‖ * ‖c * v j‖ := by simpa only [norm_mul] using norm_sum_le s (fun j => μ j * (c * v j))
    _ ≤ Real.sqrt (∑ j ∈ s, ‖μ j‖ ^ 2) * Real.sqrt (∑ j ∈ s, ‖c * v j‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ Real.sqrt (∑' j, ‖μ j‖ ^ 2) * A := by
      refine mul_le_mul (Real.sqrt_le_sqrt (hμ.sum_le_tsum s (fun _ _ => sq_nonneg _))) ?_
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_sqrt hv).trans_eq (Real.sqrt_sq hA₀)

private theorem sub_le_choose (n ℓ : ℕ) (hℓ : 0 < ℓ) (hn : ℓ ≤ n) :
    n + 1 - ℓ ≤ n.choose ℓ := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : ℓ = n + 1
    · subst ℓ
      simp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hℓ.ne'
    rw [Nat.choose_succ_succ]
    have h₁ := ih (by omega)
    have h₂ := Nat.choose_pos (n := n) (k := k) (by omega)
    omega

/-- The reciprocal tail coefficients at positive discrete weight are square summable. -/
theorem summable_sq_inv_tailMultiplier {ℓ : ℕ} (hℓ : 0 < ℓ) (ε : ℤ) {σ : ℂ}
    (hσ : ‖σ‖ = 1) : Summable fun j => ‖(tailMultiplier ℓ ε σ j)⁻¹‖ ^ 2 := by
  let majorant (j : ℤ) : ℝ := 4 ^ 2 * (1 / (j : ℝ) ^ 2)
  have hm : Summable majorant := (Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).mul_left _
  have he : ∀ᶠ j : ℤ in Filter.cofinite, 4 * ℓ + 1 ≤ j.natAbs := by
    apply Filter.eventually_cofinite.mpr
    refine (Set.finite_Icc (-(4 * (ℓ : ℤ))) (4 * (ℓ : ℤ))).subset ?_
    intro j hj
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_le] at hj ⊢
    have habs : |j| = (j.natAbs : ℤ) := Int.abs_eq_natAbs j
    rw [← abs_le, habs]
    exact_mod_cast (by omega : j.natAbs ≤ 4 * ℓ)
  apply Summable.of_norm_bounded_eventually (g := majorant) hm
  filter_upwards [he] with j hj
  let n := j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2
  have hnorm : ‖tailMultiplier ℓ ε σ j‖ = (n.choose ℓ : ℝ) := by
    by_cases h : 0 ≤ j
    · rw [tailMultiplier, extend_of_nonneg h, tailSeq, Complex.norm_natCast]
    · rw [tailMultiplier, extend_of_neg (lt_of_not_ge h), norm_mul, hσ, one_mul, tailSeq,
        Complex.norm_natCast]
  have hn : ℓ ≤ n := by dsimp [n]; omega
  have hbound : j.natAbs ≤ 4 * n.choose ℓ := by
    have hc := sub_le_choose n ℓ hℓ hn
    dsimp only [n] at hc ⊢
    omega
  have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hpos : 0 < |(j : ℝ)| := by rw [habs]; exact_mod_cast (by omega : 0 < j.natAbs)
  have hc : 0 < (n.choose ℓ : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hdiv : (n.choose ℓ : ℝ)⁻¹ ≤ 4 / |(j : ℝ)| := by
    rw [inv_eq_one_div, div_le_div_iff₀ hc hpos, one_mul, habs]
    exact_mod_cast hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_inv, hnorm]
  calc
    _ ≤ (4 / |(j : ℝ)|) ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hdiv _
    _ = majorant j := by dsimp only [majorant]; rw [div_pow, sq_abs, div_eq_mul_inv, one_div]

/-- Square-summable multipliers give compact sup-norm bounds, and the reciprocal tail
sequence has square-summable coefficients at every positive discrete weight. -/
def RealBlockFourierSupNormStatement : Prop :=
  (∀ (n p : ℕ) (ds es : List RealBlock) (ε : ℤ) (σ : ℂ) (μ : ℤ → ℂ)
    (h : IsBlockFrobData n ds es p ε σ μ), (Summable fun j => ‖μ j‖ ^ 2) →
    ∀ (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
      (g : Langlands.GeneralLinear n ℝ), g ∈ unitaryCompact ℝ n →
    ∀ A : ℝ, (∀ k ∈ unitaryCompact ℝ n, ‖f.val k‖ ≤ A) →
      ‖(blockFrobMap h f).val g‖ ≤ Real.sqrt (∑' j, ‖μ j‖ ^ 2) * A) ∧
  (∀ (ℓ : ℕ), 0 < ℓ → ∀ (ε : ℤ) (σ : ℂ), ‖σ‖ = 1 →
    Summable fun j => ‖(tailMultiplier ℓ ε σ j)⁻¹‖ ^ 2)

theorem realBlockFourierSupNorm : RealBlockFourierSupNormStatement :=
  ⟨fun _ _ _ _ _ _ _ h hμ f _ hg _ hA => norm_blockFrobMap_le h hμ f hg hA,
    fun _ hℓ ε _ hσ => summable_sq_inv_tailMultiplier hℓ ε hσ⟩

end Langlands.Archimedean.RealBlockFourierSupNorm
