import Langlands.Representation.RankinSelberg.HighlyRamified.PowerSeriesUniqueness
import Langlands.Representation.RankinSelberg.RationalContinuation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Laurent coefficients of an integral over integer shells

Let `D : Q → ℤ` have measurable fibres `S_j = {D = j}` and let `Φ` vanish where `D < j₀`.
If `∫ Φ X₀^D` converges absolutely for one positive real point `X₀ = q^(-s₀)` and
`∫ Φ X^D = K` for every `X = q^(-s)` with `Re s` large, then `∫_(S_j) Φ = K` for `j = 0`
and `0` otherwise.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory Function

/-- Every nonzero complex number is a spectral point `q^(-s)`, with
`Re s = -log ‖X‖ / log q`. -/
theorem exists_spectralPoint_eq {q : ℕ} (hq : 1 < q) {X : ℂ} (hX : X ≠ 0) :
    ∃ s : ℂ, spectralPoint q s = X ∧ s.re = -Real.log ‖X‖ / Real.log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : Real.log q ≠ 0 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq
    exact (Real.log_pos this).ne'
  have hlogC : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq0.le]
  have hlogC' : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast hlog
  refine ⟨-(Complex.log X) / (Real.log q : ℂ), ?_, ?_⟩
  · unfold spectralPoint
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne'), hlogC]
    have : (Real.log q : ℂ) * -(-Complex.log X / (Real.log q : ℂ)) = Complex.log X := by
      field_simp
    rw [this, Complex.exp_log hX]
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]

theorem norm_spectralPoint {q : ℕ} (hq : 0 < q) (s : ℂ) :
    ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
  unfold spectralPoint
  rw [Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]

variable {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) (D : Q → ℤ)

/-- Integrability of `Φ X^D` for `‖X‖ ≤ ‖X₀‖`, from integrability at `X₀`. -/
theorem integrable_zpow_of_le (hD : ∀ j, MeasurableSet {x | D x = j}) (Φ : Q → ℂ) (j₀ : ℤ)
    (hsupp : ∀ x, Φ x ≠ 0 → j₀ ≤ D x) (X₀ X : ℂ) (hX₀ : X₀ ≠ 0) (hX : X ≠ 0)
    (hle : ‖X‖ ≤ ‖X₀‖) (hint : Integrable (fun x => Φ x * X₀ ^ D x) μ) :
    Integrable (fun x => Φ x * X ^ D x) μ := by
  have hDm : Measurable D := measurable_to_countable' fun j => hD j
  set ρ : ℝ := ‖X‖ / ‖X₀‖ with hρ
  have hρ0 : 0 < ρ := div_pos (norm_pos_iff.mpr hX) (norm_pos_iff.mpr hX₀)
  have hρ1 : ρ ≤ 1 := (div_le_one (norm_pos_iff.mpr hX₀)).mpr hle
  have hmeas : AEStronglyMeasurable (fun x => Φ x * X ^ D x) μ := by
    have h1 : (fun x => Φ x * X ^ D x) =
        fun x => (Φ x * X₀ ^ D x) * (X / X₀) ^ D x := by
      funext x
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_comm (X₀ ^ D x), mul_div_assoc,
        div_self (zpow_ne_zero _ hX₀), mul_one]
    rw [h1]
    exact hint.aestronglyMeasurable.mul
      ((Measurable.of_discrete (f := fun j : ℤ => (X / X₀) ^ j)).comp hDm).aestronglyMeasurable
  refine Integrable.mono' (hint.norm.const_mul (ρ ^ j₀)) hmeas
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hΦ : Φ x = 0
  · simp [hΦ]
  · have hj := hsupp x hΦ
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow]
    have hpow : ‖X‖ ^ D x = ρ ^ D x * ‖X₀‖ ^ D x := by
      rw [hρ, div_zpow, div_mul_cancel₀ _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr hX₀))]
    rw [hpow]
    have hρle : ρ ^ D x ≤ ρ ^ j₀ := zpow_le_zpow_right_of_le_one₀ hρ0 hρ1 hj
    calc ‖Φ x‖ * (ρ ^ D x * ‖X₀‖ ^ D x) = ρ ^ D x * (‖Φ x‖ * ‖X₀‖ ^ D x) := by ring
      _ ≤ ρ ^ j₀ * (‖Φ x‖ * ‖X₀‖ ^ D x) :=
        mul_le_mul_of_nonneg_right hρle (by positivity)

/-- The shell expansion `∫ Φ X^D = Σ_j X^j ∫_(S_j) Φ`. -/
theorem hasSum_shells (hD : ∀ j, MeasurableSet {x | D x = j}) (Φ : Q → ℂ) (X : ℂ)
    (hint : Integrable (fun x => Φ x * X ^ D x) μ) :
    HasSum (fun j : ℤ => (∫ x in {x | D x = j}, Φ x ∂μ) * X ^ j)
      (∫ x, Φ x * X ^ D x ∂μ) := by
  have hdisj : Pairwise (Disjoint on fun j : ℤ => {x | D x = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hi hj => hij (hi.symm.trans hj)
  have hU : (⋃ j : ℤ, {x | D x = j}) = Set.univ := by
    ext x; simp
  have h := hasSum_integral_iUnion hD hdisj (by rw [hU]; exact hint.integrableOn)
  rw [hU, setIntegral_univ] at h
  convert h using 1
  funext j
  rw [← integral_mul_const]
  refine setIntegral_congr_fun (hD j) fun x hx => ?_
  change D x = j at hx
  rw [hx]

/-- Laurent coefficient extraction: a shell integral that is the constant `K` on a right
half-plane has `K` as its only nonzero shell coefficient, at `j = 0`. -/
theorem shell_integral_eq_of_const {q : ℕ} (hq : 1 < q)
    (hD : ∀ j, MeasurableSet {x | D x = j}) (Φ : Q → ℂ) (j₀ : ℤ)
    (hsupp : ∀ x, Φ x ≠ 0 → j₀ ≤ D x) (s₀ : ℝ)
    (hint : Integrable (fun x => Φ x * spectralPoint q s₀ ^ D x) μ) (K : ℂ) (a : ℝ)
    (hK : ∀ s : ℂ, a < s.re → ∫ x, Φ x * spectralPoint q s ^ D x ∂μ = K) (j : ℤ) :
    ∫ x in {x | D x = j}, Φ x ∂μ = if j = 0 then K else 0 := by
  have hq0 : 0 < q := by omega
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  set j₁ : ℤ := min j₀ 0 with hj₁
  have hsupp' : ∀ x, Φ x ≠ 0 → j₁ ≤ D x := fun x hx => (min_le_left _ _).trans (hsupp x hx)
  set c : ℤ → ℂ := fun j => ∫ x in {x | D x = j}, Φ x ∂μ with hc
  -- coefficients below `j₁` vanish
  have hc0 : ∀ j, j < j₁ → c j = 0 := by
    intro j hj
    simp only [hc]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    by_contra hne
    have := hsupp' x hne
    change D x = j at hx
    omega
  -- radii
  set s₁ : ℝ := max s₀ a + 1 with hs₁
  set x₀ : ℝ := (q : ℝ) ^ (-s₀) with hx₀
  have hx₀pos : 0 < x₀ := Real.rpow_pos_of_pos (by positivity) _
  have hX₀ne : spectralPoint q s₀ ≠ 0 := spectralPoint_ne_zero_of_pos hq0 _
  have hnX₀ : ‖spectralPoint q s₀‖ = x₀ := by
    rw [norm_spectralPoint hq0]; simp [hx₀]
  set r : ℝ := (q : ℝ) ^ (-s₁) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hrx₀ : r ≤ x₀ := by
    apply Real.rpow_le_rpow_of_exponent_le hq1.le
    simp only [hs₁]
    linarith [le_max_left s₀ a]
  -- the series identity on the punctured disc of radius `r`
  set k : ℕ := (-j₁).toNat with hk
  have hkj : ((k : ℕ) : ℤ) = -j₁ := by
    simp only [hk]; exact Int.toNat_of_nonneg (by simp [hj₁])
  set b : ℕ → ℂ := fun n => c ((n : ℤ) + j₁) with hb
  have hshift : ∀ X : ℂ, X ≠ 0 →
      HasSum (fun j : ℤ => c j * X ^ j) (∫ x, Φ x * X ^ D x ∂μ) →
      HasSum (fun n : ℕ => b n * X ^ n) ((∫ x, Φ x * X ^ D x ∂μ) * X ^ k) := by
    intro X hX h
    have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + j₁) := by
      intro m n hmn; simpa using hmn
    have h' := (hinj.hasSum_iff (f := fun j : ℤ => c j * X ^ j) (a := _) (fun j hj => by
      have hlt : j < j₁ := by
        by_contra hge
        apply hj
        exact ⟨(j - j₁).toNat, by simp; omega⟩
      simp [hc0 j hlt])).mpr h
    have h'' := h'.mul_right (X ^ k)
    convert h'' using 1
    funext n
    simp only [Function.comp, hb]
    rw [mul_assoc, ← zpow_natCast X k, ← zpow_add₀ hX, hkj, ← zpow_natCast X n]
    congr 2
    ring
  -- summability at radius `r`
  have hnorm_int : Integrable (fun x => ‖Φ x * spectralPoint q s₀ ^ D x‖) μ := hint.norm
  have hsumc : Summable fun j : ℤ => ‖c j‖ * x₀ ^ j := by
    have hS := hasSum_shells μ D hD (fun x => (‖Φ x‖ : ℂ)) (x₀ : ℂ) (by
      have : (fun x => (‖Φ x‖ : ℂ) * (x₀ : ℂ) ^ D x) =
          fun x => ((‖Φ x * spectralPoint q s₀ ^ D x‖ : ℝ) : ℂ) := by
        funext x
        rw [norm_mul, norm_zpow, hnX₀]
        push_cast
        ring
      rw [this]
      exact hnorm_int.ofReal)
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hS.summable.norm)
    rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hx₀pos.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc ‖c j‖ ≤ ∫ x in {x | D x = j}, ‖Φ x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ‖∫ x in {x | D x = j}, (‖Φ x‖ : ℂ) ∂μ‖ := by
        rw [integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (setIntegral_nonneg_of_ae_restrict
            (Filter.Eventually.of_forall fun _ => norm_nonneg _))]
  have hsumb : Summable fun n : ℕ => ‖b n‖ * ((⟨r, hrpos.le⟩ : NNReal) : ℝ) ^ n := by
    have hsumb0 : Summable fun n : ℕ => ‖b n‖ * x₀ ^ ((n : ℤ) + j₁) :=
      hsumc.comp_injective (fun m n hmn => by simpa using hmn)
    have hsumb1 : Summable fun n : ℕ => ‖b n‖ * x₀ ^ n := by
      have := hsumb0.mul_right (x₀ ^ (-j₁))
      refine this.congr fun n => ?_
      rw [mul_assoc, ← zpow_add₀ hx₀pos.ne', show (n : ℤ) + j₁ + -j₁ = n by ring, zpow_natCast]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsumb1
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrpos.le hrx₀ n) (norm_nonneg _)
  have hval : ∀ X : ℂ, X ≠ 0 → ‖X‖ < ((⟨r, hrpos.le⟩ : NNReal) : ℝ) →
      ∑' n, b n * X ^ n = K * X ^ k := by
    intro X hX hXr
    obtain ⟨s, hs, hsre⟩ := exists_spectralPoint_eq hq hX
    have hsre' : s₁ < s.re := by
      rw [hsre]
      rw [lt_div_iff₀ hlogq]
      have hlog : Real.log ‖X‖ < Real.log r := Real.log_lt_log (norm_pos_iff.mpr hX) hXr
      rw [hr, Real.log_rpow (by positivity)] at hlog
      linarith
    have has : a < s.re := by linarith [le_max_right s₀ a]
    have hs₀ : s₀ < s.re := by linarith [le_max_left s₀ a]
    have hle : ‖X‖ ≤ ‖spectralPoint q s₀‖ := by
      rw [hnX₀]; exact hXr.le.trans hrx₀
    have hintX := integrable_zpow_of_le μ D hD Φ j₁ hsupp' _ X hX₀ne hX hle hint
    have hS := hshift X hX (hasSum_shells μ D hD Φ X hintX)
    rw [← hs, hK s has, hs] at hS
    exact hS.tsum_eq
  have hcoeff := coeff_eq_of_tsum_eq_monomial (b := b) (r := ⟨r, hrpos.le⟩) hrpos hsumb K k hval
  -- read off the coefficient `c j`
  change c j = _
  by_cases hj : j < j₁
  · rw [hc0 j hj]
    have : j ≠ 0 := by omega
    simp only [this, ↓reduceIte]
  · have hn : ((j - j₁).toNat : ℤ) + j₁ = j := by omega
    have := hcoeff (j - j₁).toNat
    simp only [hb, hn] at this
    rw [this]
    by_cases h0 : j = 0
    · subst h0
      have : (0 - j₁).toNat = k := by omega
      simp only [this, ↓reduceIte]
    · have : (j - j₁).toNat ≠ k := by omega
      simp only [this, h0, ↓reduceIte]

end Langlands.RankinSelberg.HighlyRamified
