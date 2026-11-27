import Langlands.Global.RankinSelberg.RealGodementSpectralStep
import Langlands.Global.RankinSelberg.RealPrincipalSeriesFactors
import Langlands.Global.RankinSelberg.RealToralQuotientDensity
import Langlands.Representation.Archimedean.RealLeviLimit
import Langlands.Representation.Archimedean.RealLeviTwoBlock

/-! # Dominant spectral deformations for real discrete blocks -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviDeformation

open GramFormula RealGodement RealGodementProfiles RealInducedStandardBound
open RealIwasawa RealLeviChartIntegrable RealLeviTwoBlock RealPrincipalSeries

/-- The first position of the nonzero-weight pair containing `i`, or `i` for a singleton.
A weight-zero pair is treated as two singletons. -/
def blockStart (ds : List RealBlock) (i : ℕ) : ℕ :=
  if i ≠ 0 ∧ ∃ d, realInducedBlockAt ds (i - 1) = some d ∧ d.weight ≠ 0 then i - 1 else i

theorem blockStart_le (ds : List RealBlock) (i : ℕ) : blockStart ds i ≤ i := by
  unfold blockStart
  split <;> omega

theorem le_blockStart (ds : List RealBlock) (i : ℕ) : i - 1 ≤ blockStart ds i := by
  unfold blockStart
  split <;> omega

theorem monotone_blockStart (ds : List RealBlock) : Monotone (blockStart ds) := by
  intro i j h
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  exact (blockStart_le ds i).trans ((show i ≤ j - 1 by omega).trans (le_blockStart ds j))

theorem blockStart_of_induced {ds : List RealBlock} {i : ℕ} {d : ComplexCharacterData}
    (h : realInducedBlockAt ds i = some d) : blockStart ds i = i := by
  apply ite_eq_right
  rintro ⟨hi, e, he, _⟩
  have hn := (induced_at he).2.2.2.2.2.2
  rw [show i - 1 + 1 = i by omega, h] at hn
  contradiction

/-- Adjacent positions have the same class precisely inside a nonzero-weight pair. -/
theorem blockStart_succ_eq_iff (ds : List RealBlock) (i : ℕ) :
    blockStart ds (i + 1) = blockStart ds i ↔
      ∃ d, realInducedBlockAt ds i = some d ∧ d.weight ≠ 0 := by
  by_cases hd : ∃ d, realInducedBlockAt ds i = some d ∧ d.weight ≠ 0
  · obtain ⟨d, h, hw⟩ := hd
    have h₀ := blockStart_of_induced h
    have h₁ : blockStart ds (i + 1) = i := by
      unfold blockStart
      rw [Nat.add_sub_cancel]
      exact ite_eq_left ⟨by omega, d, h, hw⟩
    exact ⟨fun _ => ⟨d, h, hw⟩, fun _ => h₁.trans h₀.symm⟩
  have h₁ : blockStart ds (i + 1) = i + 1 := by
    unfold blockStart
    rw [Nat.add_sub_cancel]
    exact ite_eq_right (fun h => hd h.2)
  exact ⟨fun h => by have := blockStart_le ds i; omega, fun h => (hd h).elim⟩

theorem realPositionExponent_expand (ds : List RealBlock) (i : ℕ) :
    realPositionExponent (expand ds) i = realPositionExponent ds i := by
  induction ds generalizing i with
  | nil => rfl
  | cons b ds ih =>
    cases b with
    | character d =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
    | induced d =>
      rcases i with _ | _ | i
      · rfl
      · rfl
      · exact ih i

/-- Separate the classes by the spectral parameter, using the same shift on both
positions of each nonzero-weight pair. -/
def exponentPath {n : ℕ} (ds : List RealBlock) (z : Fin n → ℂ) (t : ℂ) : Fin n → ℂ :=
  fun i => z i - t * (blockStart ds i : ℂ)

@[simp] theorem exponentPath_zero {n : ℕ} (ds : List RealBlock) (z : Fin n → ℂ) :
    exponentPath ds z 0 = z := by
  funext i
  simp [exponentPath]

theorem differentiable_exponentPath {n : ℕ} (ds : List RealBlock) (z : Fin n → ℂ) :
    Differentiable ℂ (exponentPath ds z) :=
  differentiable_pi.mpr fun i => (differentiable_const (c := z i)).sub (differentiable_id.mul_const _)

theorem exponentPath_re {n : ℕ} (ds : List RealBlock) (z : Fin n → ℂ) (t : ℂ) (i : Fin n) :
    (exponentPath ds z t i).re = (z i).re - t.re * (blockStart ds i : ℝ) := by
  simp [exponentPath, Complex.mul_re, Complex.sub_re]

/-- On a nonzero-weight pair the position exponent difference is preserved. -/
theorem exponentPath_pair_gap {r : ℕ} {ds : List RealBlock}
    {p : Fin (r + 1) → Fin 2} {z : Fin (r + 1) → ℂ}
    (hds : expand ds = characterList p z) {d : ComplexCharacterData} {i : Fin r}
    (hi : realInducedBlockAt ds i = some d) (hw : d.weight ≠ 0) (t : ℂ) :
    exponentPath ds z t i.castSucc - exponentPath ds z t i.succ = (d.weight.natAbs : ℂ) := by
  have he (j : Fin (r + 1)) : z j = realPositionExponent ds j := by
    rw [← realPositionExponent_expand, hds, realPositionExponent_characterList]
  have hslot := induced_at hi
  have hlabel := (blockStart_succ_eq_iff ds i).2 ⟨d, hi, hw⟩
  simp only [exponentPath, he, Fin.val_castSucc, Fin.val_succ, hslot.2.2.1,
    hslot.2.2.2.1, hlabel]
  ring

/-- For sufficiently large real part of the parameter the position exponents are in the
strict chamber, uniformly in the imaginary part. -/
theorem exponentPath_mem_chamber {r : ℕ} {ds : List RealBlock}
    {p : Fin (r + 1) → Fin 2} {z : Fin (r + 1) → ℂ}
    (hds : expand ds = characterList p z) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℂ, T < t.re → exponentPath ds z t ∈ realSpectralChamber r := by
  let S := ∑ i : Fin (r + 1), |(z i).re|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * S, by linarith, fun t ht i => ?_⟩
  by_cases h : blockStart ds (i.val + 1) = blockStart ds i
  · obtain ⟨d, hi, hw⟩ := (blockStart_succ_eq_iff ds i).1 h
    have hg := congrArg Complex.re (exponentPath_pair_gap hds hi hw t)
    simp only [Complex.sub_re, Complex.natCast_re] at hg
    have hpos : (0 : ℝ) < d.weight.natAbs := by
      exact_mod_cast Int.natAbs_pos.mpr hw
    linarith
  have hl : blockStart ds (i.val : ℕ) < blockStart ds (i.val + 1) :=
    lt_of_le_of_ne (monotone_blockStart ds (Nat.le_succ _)) (Ne.symm h)
  have hm : (1 : ℝ) ≤ (blockStart ds (i.val + 1) : ℝ) - (blockStart ds i : ℝ) := by
    have h' : blockStart ds i + 1 ≤ blockStart ds (i.val + 1) := hl
    exact le_sub_iff_add_le.mpr (by
      rw [add_comm]
      exact_mod_cast h')
  have ht₀ : 0 ≤ t.re := by linarith
  have hmul := mul_le_mul_of_nonneg_left hm ht₀
  have hbound (j : Fin (r + 1)) : |(z j).re| ≤ S :=
    Finset.single_le_sum (f := fun i => |(z i).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h₁ := (le_abs_self (z i.succ).re).trans (hbound i.succ)
  have h₂ := (neg_le_abs (z i.castSucc).re).trans (hbound i.castSucc)
  rw [exponentPath_re, exponentPath_re]
  simp only [Fin.val_succ, Fin.val_castSucc]
  nlinarith

section GramMajorant

variable {n : ℕ} {cl : Fin n → ℕ}

private def realLabel (cl : Fin n → ℕ) (i : ℕ) : ℝ :=
  if hi : i < n then cl ⟨i, hi⟩ else 0

private def gramExponent (cl : Fin n → ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  (δ * (realLabel cl (i - 1) - realLabel cl i) - 1) / 2

private theorem realLabel_fin (cl : Fin n → ℕ) (i : Fin n) :
    realLabel cl i = cl i := dite_eq_left i.isLt

private theorem realLabel_pred_le (hcl : Monotone cl) (i : Fin n) :
    realLabel cl ((i : ℕ) - 1) ≤ realLabel cl i := by
  have hi : (i : ℕ) - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
  rw [realLabel_fin, realLabel, dite_eq_left hi]
  exact_mod_cast hcl (show (⟨(i : ℕ) - 1, hi⟩ : Fin n) ≤ i from Nat.sub_le _ _)

private theorem norm_expFun_eq (e : ℕ → ℝ) (g : Langlands.GeneralLinear n ℝ) :
    ‖expFun n e g‖ = Real.exp (torusModularLog n (alpha g) / 2 + ∑ i : Fin n, alpha g i * e i) := by
  change ‖standardSection (fun i : Fin n => (e i : ℂ)) 1 g‖ = _
  rw [standardSection_eq, Pi.one_apply, mul_one, Complex.norm_exp, Complex.re_sum,
    torusModularLog_apply, Finset.sum_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ((alpha g i : ℂ) * ((e i : ℂ) + (((n : ℂ) - 1) / 2 - (i.val : ℂ)))).re = _
  norm_num [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.div_re, Complex.normSq_ofNat]
  ring

private theorem norm_expFun_le (hcl : Monotone cl) (τ : ℝ) (X : CoordC cl → ℝ) :
    ‖expFun n (fun i => -(τ * realLabel cl i)) (lowerCGL hcl X)‖ ≤
      ∏ l : Fin n, gram l (lowerC cl X) ^ gramExponent cl τ l := by
  let e (i : ℕ) := -(τ * realLabel cl i)
  have hB : ∀ k ∈ unitaryCompact ℝ n, ‖expFun n e k‖ ≤ 1 := by
    intro k hk
    have h := expFun_mul n e 1 hk
    rw [one_mul, expFun_one] at h
    rw [h, norm_one]
  have hg : gram 0 (lowerCGL hcl X).val = 1 := by
    rw [lowerCGL_val, RealLeviTorus.gram_zero_eq, det_lowerC hcl, one_pow]
  have h := RealLeviTorus.norm_le_gram_fin
    (σ := fun i => e i + ((n : ℝ) - 1) / 2 - (i : ℝ))
    (expFun_mem n e).2 (fun a => by
      rw [PartialJacquet.norm_principalSeriesCharacter (RealLeviLimit.isSignedPower_absChar e)]
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1) hB (lowerCGL hcl X) hg (one_mem (unitaryCompact ℝ n)) (fun l => gramExponent cl τ l)
    (fun l hl => by
      unfold gramExponent e
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr hl), Nat.cast_one]
      ring)
  simpa only [mul_one, one_mul, lowerCGL_val, e] using h

private theorem gram_one_le (hcl : Monotone cl) (X : CoordC cl → ℝ) (l : ℕ) :
    1 ≤ gram l (lowerC cl X) :=
  RealLeviChart.one_le_gram_of_lower (lowerC_isLowerTriangular hcl X)
    (fun i => by simp [lowerC]) l

/-- The spectral weight from the Borel half-modulus and a decreasing real block shift
has a common integrable majorant on the opposite radical for all `τ ≥ δ > 0`. -/
def RealLeviDeformationMajorantStatement : Prop :=
  ∀ (n : ℕ) (cl : Fin n → ℕ) (hcl : Monotone cl) (δ : ℝ), 0 < δ →
    ∃ B : (CoordC cl → ℝ) → ℝ, Continuous B ∧ Integrable B ∧
      ∀ (τ : ℝ), δ ≤ τ → ∀ (X : CoordC cl → ℝ),
        let y := alpha (lowerCGL hcl X)
        Real.exp (torusModularLog n y / 2 - τ * ∑ i, y i * (cl i : ℝ)) ≤ B X

theorem realLeviDeformationMajorant : RealLeviDeformationMajorantStatement := by
  intro n cl hcl δ hδ
  let B (X : CoordC cl → ℝ) := ∏ l : Fin n, gram l (lowerC cl X) ^ gramExponent cl δ l
  have hB : Continuous B := continuous_prod_gram hcl _
  have hG (X : CoordC cl → ℝ) (l : Fin n) := gram_one_le hcl X l
  have hB₀ (X : CoordC cl → ℝ) : 0 ≤ B X :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (zero_le_one.trans (hG X i)) _
  have hI : Integrable B := by
    refine ⟨hB.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hB₀)]
    refine gen n cl hcl _ (fun l _ => ?_) (fun k l hk hl => ?_)
    · have h := mul_nonpos_of_nonneg_of_nonpos hδ.le (sub_nonpos.mpr (realLabel_pred_le hcl l))
      unfold gramExponent
      linarith
    · have he : (l : ℕ) - 1 = k := by omega
      have hlt : realLabel cl k < realLabel cl l := by
        rw [realLabel_fin, realLabel_fin]
        exact_mod_cast hl
      have h := mul_neg_of_pos_of_neg hδ (sub_neg.mpr hlt)
      unfold gramExponent
      rw [he]
      linarith
  refine ⟨B, hB, hI, fun τ hτ X => ?_⟩
  let y := alpha (lowerCGL hcl X)
  have he : (∑ i : Fin n, y i * -(τ * realLabel cl i)) =
      -(τ * ∑ i : Fin n, y i * (cl i : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [realLabel_fin]; ring
  change Real.exp (torusModularLog n y / 2 - τ * ∑ i, y i * (cl i : ℝ)) ≤ B X
  rw [sub_eq_add_neg, ← he, ← norm_expFun_eq (fun i => -(τ * realLabel cl i)) (lowerCGL hcl X)]
  apply (norm_expFun_le hcl τ X).trans
  refine Finset.prod_le_prod₀ (fun l _ => Real.rpow_nonneg (zero_le_one.trans (hG X l)) _) ?_
  intro l _
  apply Real.rpow_le_rpow_of_exponent_le (hG X l)
  have h := mul_le_mul_of_nonpos_right hτ (sub_nonpos.mpr (realLabel_pred_le hcl l))
  unfold gramExponent
  linarith

end GramMajorant

end Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviDeformation
