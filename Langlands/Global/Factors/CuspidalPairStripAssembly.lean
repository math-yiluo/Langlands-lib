import Langlands.Global.Factors.CuspidalPairPoleContinuation
import Langlands.Global.Factors.CuspidalPairStripAnalysis
import Langlands.Global.Factors.CuspidalPairRightStripBounds

/-! # Transfer of vertical-strip bounds to a completed pair function -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Asymptotics Filter NumberField Set

namespace Langlands.Global.CuspidalPairPoles

open LocalFactor.Archimedean

private theorem away_of_norm_le {s : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h0 : ε ≤ ‖s‖) (h1 : ε ≤ ‖s - 1‖) : s ∉ ({0, 1} : Set ℂ) := by
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨fun h => by simpa [h] using hε.trans_le h0,
    fun h => by simpa [h] using hε.trans_le h1⟩

private theorem stripGrowth_regularized_product {R I Λ : ℂ → ℂ}
    (hI : IsBoundedInVerticalStrips I)
    (heq : ∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s)
    (hreg : ∀ s ∉ ({0, 1} : Set ℂ), regularizeSimplePoles Λ s = s * (s - 1) * Λ s) :
    HasStripExponentialGrowth (R * regularizeSimplePoles Λ) := by
  intro a b
  obtain ⟨C, hC⟩ := hI a b 1 zero_lt_one
  let A := max |a| |b|
  have hA : 0 ≤ A := (abs_nonneg a).trans (le_max_left _ _)
  refine ⟨(A + 1) * (A + 2) * max C 0, 2, 1, by positivity, by norm_num, ?_⟩
  intro s hL hR ht
  have hsRe : |s.re| ≤ A := by
    apply abs_le.mpr
    dsimp only [A]
    constructor
    · linarith [neg_abs_le a, le_max_left |a| |b|]
    · linarith [le_abs_self b, le_max_right |a| |b|]
  have h0 := ht.trans (Complex.abs_im_le_norm s)
  have h1 := ht.trans (by simpa using Complex.abs_im_le_norm (s - 1))
  have hs := away_of_norm_le zero_lt_one h0 h1
  have hI' := (hC s hL hR h0 h1).trans (le_max_left C 0)
  have hpoly (z : ℂ) (X : ℝ) (hX : 0 ≤ X) (hz : |z.re| ≤ X) :
      ‖z‖ ≤ (X + 1) * Real.exp |z.im| := by
    calc
      _ ≤ X + |z.im| := (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add_left hz _)
      _ ≤ (X + 1) * (|z.im| + 1) := by nlinarith [mul_nonneg hX (abs_nonneg z.im)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
  have hnorm₀ := hpoly s A hA hsRe
  have hnorm₁ : ‖s - 1‖ ≤ (A + 2) * Real.exp |s.im| := by
    have h' : |(s - 1).re| ≤ A + 1 := by
      simpa only [Complex.sub_re, Complex.one_re, abs_one] using
        (abs_sub s.re (1 : ℝ)).trans (add_le_add_left hsRe |(1 : ℝ)|)
    simpa only [Complex.sub_im, Complex.one_im, sub_zero, add_assoc, one_add_one_eq_two]
      using hpoly (s - 1) (A + 1) (by positivity) h'
  change ‖R s * regularizeSimplePoles Λ s‖ ≤ _
  rw [hreg s hs, ← mul_assoc, mul_comm (R s), mul_assoc, ← heq s hs, norm_mul, norm_mul]
  calc
    _ ≤ ((A + 1) * Real.exp |s.im|) * ((A + 2) * Real.exp |s.im|) * max C 0 := by
      gcongr
    _ = _ := by rw [two_mul, Real.exp_add]; ring

private theorem norm_add_div_norm_le {z w : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ε ≤ ‖z‖) :
    ‖z + w‖ / ‖z‖ ≤ 1 + ‖w‖ / ε := by
  have hn := hε.trans_le hz
  calc
    _ ≤ (‖z‖ + ‖w‖) / ‖z‖ := div_le_div_of_nonneg_right (norm_add_le z w) hn.le
    _ = 1 + ‖w‖ / ‖z‖ := by rw [add_div, div_self hn.ne']
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (norm_nonneg _) hε hz) _

/-- A single normalized test with exponential growth suffices for strip bounds
when the test integral has strip bounds and the completion is bounded on arbitrarily
far left and right boundary lines. -/
def CompletionStripBoundsFromTest : Prop :=
  ∀ (I R Λ : ℂ → ℂ) (cond : Prop),
    IsBoundedInVerticalStrips I → Differentiable ℂ R → (∃ z, R z ≠ 0) →
    HasStripExponentialGrowth R → HasSimplePoleProfile Λ cond →
    (∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s) →
    (∀ a : ℝ, ∃ l < a, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = l → ‖Λ s‖ ≤ C) →
    (∀ b : ℝ, ∃ r > b, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = r → ‖Λ s‖ ≤ C) →
    IsBoundedInVerticalStrips Λ

theorem completionStripBoundsFromTest : CompletionStripBoundsFromTest := by
  intro I R Λ cond hI hR hRne hRg hΛ hMatch hLeft hRight a b ε hε
  obtain ⟨hHa, hReg, _⟩ :=
    regularizeSimplePoles_spec hΛ.1 fun p hp => ⟨(hΛ.2 p hp).1, (hΛ.2 p hp).2.1⟩
  let H := regularizeSimplePoles Λ
  obtain ⟨l, hl, Cₗ, hCₗ, hLeftBound⟩ := hLeft (min a (-1))
  obtain ⟨r, hr, Cᵣ, hCᵣ, hRightBound⟩ := hRight (max b 2)
  have hla : l ≤ a := hl.le.trans (min_le_left _ _)
  have hrb : b ≤ r := (le_max_left _ _).trans hr.le
  have hl₀ : l < 0 := (hl.trans_le (min_le_right _ _)).trans (by norm_num)
  have hr₁ : 1 < r := (by norm_num : (1 : ℝ) < 2).trans_le ((le_max_right _ _).trans hr.le)
  have hlr : l < r := by linarith
  let d : ℂ := (r + 1 : ℝ)
  let f (s : ℂ) := H s / (s - d) ^ 2
  have hdRe : d.re = r + 1 := Complex.ofReal_re _
  have hd {s : ℂ} (hs : s.re ≤ r) : 1 ≤ ‖s - d‖ := by
    apply le_trans _ (Complex.abs_re_le_norm (s - d))
    rw [Complex.sub_re, hdRe]
    exact (show (1 : ℝ) ≤ -(s.re - (r + 1)) by linarith).trans (neg_le_abs _)
  have hdne {s : ℂ} (hs : s.re ≤ r) : s - d ≠ 0 :=
    norm_pos_iff.mp (zero_lt_one.trans_le (hd hs))
  have hf : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo l r) := by
    have hDiff : DifferentiableOn ℂ f {s : ℂ | s.re ≤ r} := by
      intro s hs
      have hden : DifferentiableAt ℂ (fun s : ℂ => (s - d) ^ 2) s := by fun_prop
      exact ((hHa s (mem_univ s)).differentiableAt.div hden (pow_ne_zero _ (hdne hs))).differentiableWithinAt
    exact (hDiff.mono (closure_minimal (fun s hs => (show s.re ∈ Ioo l r from hs).2.le)
      (isClosed_le Complex.continuous_re continuous_const))).diffContOnCl
  let k := (Real.pi / (r - l)) / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hk' : k < Real.pi / (r - l) := by dsimp [k]; linarith [div_pos Real.pi_pos (sub_pos.mpr hlr)]
  have hH : Differentiable ℂ H := fun s => (hHa s (mem_univ s)).differentiableAt
  obtain ⟨M, hM, hGrowth⟩ := entireQuotientStripGrowth R H hR hH
    hRne hRg (stripGrowth_regularized_product hI hMatch hReg) l r k hk
  have hfGrowth : ∃ k < Real.pi / (r - l), ∃ M,
      f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo l r)]
        fun s => Real.exp (M * Real.exp (k * |s.im|)) := by
    refine ⟨k, hk', M, IsBigO.of_bound' ?_⟩
    filter_upwards [show ∀ᶠ s : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo l r), s ∈ Complex.re ⁻¹' Ioo l r from
      mem_inf_of_right (mem_principal_self _)] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans ?_ (hGrowth s hs.1.le hs.2.le)
    change ‖H s / (s - d) ^ 2‖ ≤ _
    rw [norm_div, norm_pow]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (hd hs.2.le))
  have hAway {s : ℂ} (h : s.re < 0 ∨ 1 < s.re) : s ∉ ({0, 1} : Set ℂ) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => by rw [he, Complex.zero_re] at h; rcases h with h | h <;> linarith,
      fun he => by rw [he, Complex.one_re] at h; rcases h with h | h <;> linarith⟩
  let B := (1 + ‖d‖) * (1 + ‖d - 1‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfBound {s : ℂ} (hs : s.re ≤ r) (ha : s ∉ ({0, 1} : Set ℂ)) :
      ‖f s‖ ≤ B * ‖Λ s‖ := by
    have h₀ := norm_add_div_norm_le (w := d) zero_lt_one (hd hs)
    have h₁ := norm_add_div_norm_le (w := d - 1) zero_lt_one (hd hs)
    rw [sub_add_cancel, div_one] at h₀
    rw [show s - d + (d - 1) = s - 1 by ring, div_one] at h₁
    change ‖regularizeSimplePoles Λ s / (s - d) ^ 2‖ ≤ _
    rw [hReg s ha, norm_div, norm_mul, norm_mul, norm_pow]
    calc
      _ = (‖s‖ / ‖s - d‖) * (‖s - 1‖ / ‖s - d‖) * ‖Λ s‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul h₀ h₁ (by positivity) (by positivity)) (norm_nonneg _)
  have hfL (s : ℂ) (hs : s.re = l) : ‖f s‖ ≤ B * max Cₗ Cᵣ :=
    (hfBound (hs.le.trans hlr.le) (hAway (Or.inl (hs ▸ hl₀)))).trans
      (mul_le_mul_of_nonneg_left ((hLeftBound s hs).trans (le_max_left _ _)) hB)
  have hfR (s : ℂ) (hs : s.re = r) : ‖f s‖ ≤ B * max Cₗ Cᵣ :=
    (hfBound hs.le (hAway (Or.inr (hs ▸ hr₁)))).trans
      (mul_le_mul_of_nonneg_left ((hRightBound s hs).trans (le_max_right _ _)) hB)
  refine ⟨(1 + ‖d‖ / ε) * (1 + ‖1 - d‖ / ε) * (B * max Cₗ Cᵣ), fun s hsA hsB h0 h1 => ?_⟩
  have hsR := hsB.trans hrb
  have hs := away_of_norm_le hε h0 h1
  have hsBound := PhragmenLindelof.vertical_strip hf hfGrowth hfL hfR (hla.trans hsA) hsR
  have h₀ := norm_add_div_norm_le (w := -d) hε h0
  have h₁ := norm_add_div_norm_le (w := 1 - d) hε h1
  rw [← sub_eq_add_neg, norm_neg] at h₀
  rw [show s - 1 + (1 - d) = s - d by ring] at h₁
  calc
    ‖Λ s‖ = (‖s - d‖ / ‖s‖) * (‖s - d‖ / ‖s - 1‖) * ‖f s‖ := by
      dsimp only [f, H]
      rw [hReg s hs, norm_div, norm_mul, norm_mul, norm_pow]
      field_simp [(hε.trans_le h0).ne', (hε.trans_le h1).ne',
        (zero_lt_one.trans_le (hd hsR)).ne']
    _ ≤ _ := mul_le_mul (mul_le_mul h₀ h₁ (by positivity) (by positivity))
      hsBound (norm_nonneg _) (by positivity)

universe u uQ

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

/-- Apply the test criterion to the actual initial Euler product, whose
right-line bounds are supplied by absolute convergence and the Gamma integral. -/
theorem isBoundedInVerticalStrips_of_completed_test {c : FinitePairLChoice P P' h h'}
    {dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock}
    {dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData}
    {I R Λ : ℂ → ℂ} {cond : Prop}
    (hI : IsBoundedInVerticalStrips I) (hR : Differentiable ℂ R) (hne : ∃ z, R z ≠ 0)
    (hRg : HasStripExponentialGrowth R) (hΛ : HasSimplePoleProfile Λ cond)
    (hMatch : ∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s)
    (hLeft : ∀ a : ℝ, ∃ l < a, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = l → ‖Λ s‖ ≤ C)
    (hCompleted : c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ) :
    IsBoundedInVerticalStrips Λ := by
  refine completionStripBoundsFromTest I R Λ cond hI hR hne hRg hΛ hMatch hLeft ?_
  obtain ⟨σ, hσ⟩ := completedPairRightStripBounds F r t T T' P P' h h' c dR dR' dC dC' Λ hCompleted
  intro b
  let r := max σ b + 1
  have hr : σ < r := (le_max_left _ _).trans_lt (lt_add_one _)
  obtain ⟨C, hC, hCb⟩ := hσ r r hr
  exact ⟨r, (le_max_right _ _).trans_lt (lt_add_one _), C, hC, fun s hs => hCb s hs.ge hs.le⟩

end Langlands.Global.CuspidalPairPoles
