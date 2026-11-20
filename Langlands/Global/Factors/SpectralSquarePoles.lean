import Langlands.Analysis.LandauMeromorphicExp
import Langlands.Global.Factors.SpectralSquareDivergence

/-! # Pole detection for the exponential of a squared power-trace series -/

noncomputable section

set_option autoImplicit false

universe u

open Filter Topology

namespace Langlands.Global

open NumberField
open Unramified (Eigenvalues)
open GeneralDirichlet (SummableAt series meromorphicExpLandau)
open CuspidalPairAbsoluteConvergence (logExponent log_two_le_logExponent)
open SpectralSquare (coeff coeff_nonneg)

namespace SpectralSquare

/-- If a meromorphic continuation of the exponential of the squared power-trace
series has at most one real pole in the positive half-plane, at `1`, that pole
must occur. -/
def PoleDetectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F)) (n : ℕ), 0 < n →
    ∀ A : {v : FinitePlace F // v ∉ S} → Eigenvalues n,
      (∀ v, ∃ a ∈ (A v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖) →
      ∀ {σ₁ : ℝ}, SummableAt (coeff A) logExponent σ₁ →
        ∀ {L : ℂ → ℂ}, MeromorphicOn L {s : ℂ | 0 < s.re} →
          (∀ s : ℂ, σ₁ < s.re → L s = Complex.exp (series (coeff A) logExponent s)) →
          (∀ σ : ℝ, 0 < σ → σ ≠ 1 → 0 ≤ meromorphicOrderAt L (σ : ℂ)) →
          meromorphicOrderAt L 1 < 0

theorem poleDetection : PoleDetectionStatement.{u} := by
  intro F _ _ S n hn A hA σ₁ hsum L hL hEq hOrd
  by_contra! h
  have hOrd' (σ : ℝ) (hσ : 0 < σ) : 0 ≤ meromorphicOrderAt L (σ : ℂ) := by
    by_cases h1 : σ = 1
    · simpa only [h1, Complex.ofReal_one] using h
    · exact hOrd σ hσ h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
  exact spectralSquareDivergence F S n hn A hA
    (meromorphicExpLandau
      (fun x => (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans (log_two_le_logExponent x))
      (coeff_nonneg A) hsum hL hOrd' hEq _ (inv_pos.mpr (mul_pos hn' hD)))

private theorem real_tendsto_punctured_one :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa only [Complex.ofReal_one] using hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h : σ ≠ 1 := ne_of_gt (show 1 < σ from hσ)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ← Complex.ofReal_one,
      Complex.ofReal_inj] using h

private theorem order_pos_of_norm_tendsto_right_zero {f : ℂ → ℂ} (hf : MeromorphicAt f 1)
    (h : Tendsto (fun σ : ℝ => ‖f (σ : ℂ)‖) (𝓝[>] 1) (𝓝 0)) :
    0 < meromorphicOrderAt f 1 := by
  by_contra! hOrd
  rcases hOrd.eq_or_lt with h0 | hneg
  · obtain ⟨c, hc, hlim⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf h0
    exact hc (norm_eq_zero.mp (tendsto_nhds_unique
      (hlim.comp real_tendsto_punctured_one).norm h))
  · exact (not_tendsto_atTop_of_tendsto_nhds h)
      ((tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).comp
        real_tendsto_punctured_one)

private theorem one_le_of_pos {a : WithTop ℤ} (h : 0 < a) : 1 ≤ a := by
  cases a with
  | top => exact le_top
  | coe a =>
    have ha : (0 : ℤ) < a := WithTop.coe_lt_coe.mp h
    exact WithTop.coe_le_coe.mpr (show (1 : ℤ) ≤ a by omega)

/-- The first cross-factor has order zero at `1` if it has nonnegative order there,
the cross-factors have equal norms on the real ray, and the four-factor product
is the exponential of a squared power-trace series. -/
theorem crossOrder_eq_zero {F : Type u} [Field F] [NumberField F] {S : Finset (FinitePlace F)}
    {n : ℕ} (hn : 0 < n) (A : {v : FinitePlace F // v ∉ S} → Eigenvalues n)
    (hA : ∀ v, ∃ a ∈ (A v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖)
    {σ₁ : ℝ} (hsum : SummableAt (coeff A) logExponent σ₁)
    {U V P Q : ℂ → ℂ}
    (hU : MeromorphicOn U {s : ℂ | 0 < s.re}) (hV : MeromorphicOn V {s : ℂ | 0 < s.re})
    (hP : MeromorphicOn P {s : ℂ | 0 < s.re}) (hQ : MeromorphicOn Q {s : ℂ | 0 < s.re})
    (hU₁ : -1 ≤ meromorphicOrderAt U 1) (hV₁ : -1 ≤ meromorphicOrderAt V 1)
    (hP₁ : 0 ≤ meromorphicOrderAt P 1)
    (hOther : ∀ σ : ℝ, 0 < σ → σ ≠ 1 →
      0 ≤ meromorphicOrderAt U (σ : ℂ) ∧ 0 ≤ meromorphicOrderAt V (σ : ℂ) ∧
      0 ≤ meromorphicOrderAt P (σ : ℂ) ∧ 0 ≤ meromorphicOrderAt Q (σ : ℂ))
    (hNorm : ∀ σ : ℝ, 1 < σ → ‖P (σ : ℂ)‖ = ‖Q (σ : ℂ)‖)
    (hEq : ∀ s : ℂ, σ₁ < s.re →
      U s * V s * (P s * Q s) = Complex.exp (series (coeff A) logExponent s)) :
    meromorphicOrderAt P 1 = 0 := by
  let L : ℂ → ℂ := fun s => U s * V s * (P s * Q s)
  have hL : MeromorphicOn L {s : ℂ | 0 < s.re} := (hU.mul hV).mul (hP.mul hQ)
  have hord {z : ℂ} (hz : 0 < z.re) :
      meromorphicOrderAt L z =
        (meromorphicOrderAt U z + meromorphicOrderAt V z) +
          (meromorphicOrderAt P z + meromorphicOrderAt Q z) := by
    have hUz := hU z hz
    have hVz := hV z hz
    have hPz := hP z hz
    have hQz := hQ z hz
    exact (meromorphicOrderAt_mul (hUz.mul hVz) (hPz.mul hQz)).trans
      (congrArg₂ (· + ·) (meromorphicOrderAt_mul hUz hVz) (meromorphicOrderAt_mul hPz hQz))
  have hLt : meromorphicOrderAt L 1 < 0 := poleDetection F S n hn A hA hsum hL hEq
    (fun σ hσ hne => by
      obtain ⟨hU', hV', hP', hQ'⟩ := hOther σ hσ hne
      rw [hord (by simpa only [Complex.ofReal_re] using hσ)]
      exact add_nonneg (add_nonneg hU' hV') (add_nonneg hP' hQ'))
  refine hP₁.antisymm' (not_lt.mp fun hpos => ?_)
  have hpLim : Tendsto (fun σ : ℝ => ‖P (σ : ℂ)‖) (𝓝[>] 1) (𝓝 0) := by
    simpa only [norm_zero, Function.comp_apply] using ((tendsto_zero_of_meromorphicOrderAt_pos hpos).comp
      real_tendsto_punctured_one).norm
  have hqLim : Tendsto (fun σ : ℝ => ‖Q (σ : ℂ)‖) (𝓝[>] 1) (𝓝 0) := by
    apply hpLim.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact hNorm σ hσ
  have hRe : 0 < (1 : ℂ).re := by simp
  have hq := order_pos_of_norm_tendsto_right_zero (hQ 1 hRe) hqLim
  have hge : 0 ≤ meromorphicOrderAt L 1 := by
    rw [hord hRe]
    calc
      0 = ((-1 : WithTop ℤ) + -1) + (1 + 1) := by
        change ((0 : ℤ) : WithTop ℤ) =
          (((-1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ)) +
            (((1 : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ))
        rw [← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_eq_coe]
        norm_num
      _ ≤ _ := add_le_add (add_le_add hU₁ hV₁)
        (add_le_add (one_le_of_pos hpos) (one_le_of_pos hq))
  exact (not_lt_of_ge hge) hLt

end SpectralSquare

end Langlands.Global
