import Langlands.Global.RankinSelberg.RealGodementHaar
import Langlands.Global.RankinSelberg.RealMatrixConvergence
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord

/-! # Schwartz domination of the leading rectangle in the real gap recurrence -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapLeadingSchwartz

open ArchimedeanLocal (realNormalizedAbs)
open Langlands.RankinSelberg.GLDeterminantDensity (forwardWeight integrable_forwardWeight_iff_of_eq_smul)
open RealPlaceRestriction (norm_entry_le_realMatrixHeight two_le_realMatrixHeight realMatrixHeight_inv)
open RealGodement (realMatrixVolume realMatrixHaar exists_realMatrixHaar_eq_smul)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "H" => realMatrixHeight

/-- Stack a leading square matrix and its lower rectangle along their rows. -/
def leadingStack {k d : ℕ} (A : Mat k k) (Y : Mat d k) : Mat (k + d) k :=
  fun i j => Fin.append (fun l => A l j) (fun l => Y l j) i

private theorem norm_le_of_nnnorm_le {m n m' n' : ℕ} {A : Mat m n} {B : Mat m' n'} (h : ‖A‖₊ ≤ ‖B‖₊) :
    ‖A‖ ≤ ‖B‖ := by
  have := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm] using this

private theorem norm_leading_left {k d : ℕ} (A : Mat k k) (Y : Mat d k) :
    ‖A‖ ≤ ‖leadingStack A Y‖ := by
  apply norm_le_of_nnnorm_le
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => le_trans (le_of_eq ?_)
    (Finset.le_sup (f := fun i => ∑ j, ‖leadingStack A Y i j‖₊) (Finset.mem_univ (i.castAdd d)))
  simp only [leadingStack, Fin.append_left]

private theorem norm_leading_right {k d : ℕ} (A : Mat k k) (Y : Mat d k) :
    ‖Y‖ ≤ ‖leadingStack A Y‖ := by
  apply norm_le_of_nnnorm_le
  rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => le_trans (le_of_eq ?_)
    (Finset.le_sup (f := fun i => ∑ j, ‖leadingStack A Y i j‖₊) (Finset.mem_univ (i.natAdd k)))
  simp only [leadingStack, Fin.append_right]

/-- An entry is bounded by the row-sum operator norm. -/
theorem norm_entry_le_opNorm {m n : ℕ} (X : Mat m n) (i : Fin m) (j : Fin n) : ‖X i j‖ ≤ ‖X‖ := by
  have h : ‖X i j‖₊ ≤ ‖X‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (f := fun j => ‖X i j‖₊) (fun _ _ => bot_le)
      (Finset.mem_univ j)).trans (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))
  have := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm] using this

private theorem norm_mul_le_rank {n k : ℕ} (A : Mat n n) (B : Mat n k) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A * B‖ ≤ (n : ℝ) * C * ‖B‖ := by
  have hA' : ‖A‖₊ ≤ (n : ℝ≥0) * ⟨C, hC⟩ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc
      ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, (⟨C, hC⟩ : ℝ≥0) :=
        Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact hA i j
      _ = _ := by simp
  have hA'' : ‖A‖ ≤ (n : ℝ) * C := by
    have := NNReal.coe_le_coe.mpr hA'
    rw [coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast] at this
    exact this
  calc
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := Matrix.linfty_opNorm_mul A B
    _ ≤ (n : ℝ) * C * ‖B‖ := mul_le_mul_of_nonneg_right hA'' (norm_nonneg _)

/-- A Schwartz test on the stacked rectangle gives simultaneous polynomial decay in its
square and rectangular input, at the cost of a power of the height of the left multiplier. -/
def RealGapLeadingSchwartzStatement : Prop :=
  ∀ (k d : ℕ), 0 < k + d → ∀ (Φ : 𝓢(Mat (k + d) k, ℂ)) (p q : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G (k + d)) (A : Mat k k) (Y : Mat d k),
      ‖Φ (g.val * leadingStack A Y)‖ ≤ C * H g ^ (p + q) /
        ((1 + ‖A‖) ^ p * (1 + ‖Y‖) ^ q)

theorem realGapLeadingSchwartz : RealGapLeadingSchwartzStatement := by
  intro k d hn Φ p q
  let n := k + d
  let m := p + q
  let S := (Finset.Iic (m, 0)).sup (schwartzSeminormFamily ℝ (Mat n k) ℂ) Φ
  have hS : 0 ≤ S := apply_nonneg _ _
  refine ⟨(2 : ℝ) ^ m * S * (n : ℝ) ^ m, by positivity, fun g A Y => ?_⟩
  let B := g.val * leadingStack A Y
  let L := (n : ℝ) * H g
  have hH : 1 ≤ H g := (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_realMatrixHeight hn g)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) hH
  have hB : g⁻¹.val * B = leadingStack A Y := by
    dsimp only [B]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hNorm : ‖leadingStack A Y‖ ≤ L * ‖B‖ := by
    rw [← hB]
    apply norm_mul_le_rank _ _ (zero_le_one.trans hH)
    intro i j
    simpa only [realMatrixHeight_inv] using norm_entry_le_realMatrixHeight hn g⁻¹ i j
  have hAdd (x : ℝ) (hx : x ≤ ‖leadingStack A Y‖) : 1 + x ≤ L * (1 + ‖B‖) := by
    rw [mul_add, mul_one]
    exact add_le_add hL (hx.trans hNorm)
  have h₁ := pow_le_pow_left₀ (by positivity) (hAdd ‖A‖ (norm_leading_left A Y)) p
  have h₂ := pow_le_pow_left₀ (by positivity) (hAdd ‖Y‖ (norm_leading_right A Y)) q
  have hDecay := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0))
    le_rfl le_rfl Φ B
  rw [norm_iteratedFDeriv_zero] at hDecay
  change ‖Φ B‖ ≤ (2 : ℝ) ^ m * S * (n : ℝ) ^ m * H g ^ m /
    ((1 + ‖A‖) ^ p * (1 + ‖Y‖) ^ q)
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ ‖Φ B‖ * ((L * (1 + ‖B‖)) ^ p * (L * (1 + ‖B‖)) ^ q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h₁ h₂ (by positivity) (by positivity)) (norm_nonneg _)
    _ = L ^ m * ((1 + ‖B‖) ^ m * ‖Φ B‖) := by rw [← pow_add, mul_pow]; ring
    _ ≤ L ^ m * ((2 : ℝ) ^ m * S) := mul_le_mul_of_nonneg_left hDecay (by dsimp only [L]; positivity)
    _ = _ := by dsimp only [L]; rw [mul_pow]; ring

local instance gapLeadingGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapLeadingGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapLeadingGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance gapLeadingGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace
local instance gapLeadingVolume (n : ℕ) : (realMatrixVolume n).IsAddHaarMeasure := by
  unfold realMatrixVolume
  infer_instance

/-- Radial polynomial decay in the additive matrix space. -/
def matrixDecay {m n : ℕ} (p : ℕ) (X : Mat m n) : ℝ := ((1 + ‖X‖) ^ p)⁻¹

private theorem integrable_haarMatrixTail {n p : ℕ} (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hp : Module.finrank ℝ (Mat n n) < p) :
    Integrable (fun g : G n => realNormalizedAbs g.val.det ^ n * matrixDecay p g.val) μ := by
  have hT : Integrable (matrixDecay p : Mat n n → ℝ) (realMatrixVolume n) := by
    refine (integrable_one_add_norm (μ := realMatrixVolume n) (r := (p : ℝ))
      (by exact_mod_cast hp)).congr ?_
    exact ae_of_all _ fun X => by
      simp only [matrixDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖X‖), Real.rpow_natCast]
  obtain ⟨c, hc, hμ⟩ := exists_realMatrixHaar_eq_smul μ
  unfold realMatrixHaar at hμ
  have h := (integrable_forwardWeight_iff_of_eq_smul (K := ℝ) (E := ℝ) n nnnormHom continuous_nnnorm
    (realMatrixVolume n) μ c hc hμ (matrixDecay p)).2 hT.integrableOn
  simpa only [forwardWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, nnnormHom_apply,
    coe_nnnorm, Real.norm_eq_abs, realNormalizedAbs] using h

/-- One leading square factor of the joint kernel, with the height from the translated
small Whittaker vector and an independently chosen determinant power. -/
def weightedMatrixTail {n : ℕ} (M p : ℕ) (s : ℝ) (g : G n) : ℝ :=
  H g ^ M * realNormalizedAbs g.val.det ^ s * matrixDecay p g.val

/-- The square factor is Haar integrable at any sufficiently large real determinant power
with a sufficiently large additive matrix decay order. -/
theorem exists_integrable_weightedMatrixTail (r M : ℕ) (μ : Measure (G (r + 1))) [μ.IsHaarMeasure]
    (s : ℝ) (hs : (r + 1 : ℕ) + 2 * (M : ℝ) ≤ s) :
    ∃ p : ℕ, Integrable (weightedMatrixTail M p s) μ := by
  let n := r + 1
  let p₀ := Module.finrank ℝ (Mat n n) + 1
  let τ := s - (n : ℝ) - 2 * (M : ℝ)
  have hτ : 0 ≤ τ := by dsimp only [τ, n]; linarith
  obtain ⟨j, hj⟩ := exists_nat_ge τ
  let L := 2 * (n + 1) * M + n * j
  let C := 2 * (n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2
  let D := (n.factorial : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 1 ≤ D := by dsimp only [D]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hs₀ : 0 ≤ s := (by positivity : 0 ≤ (r + 1 : ℕ) + 2 * (M : ℝ)).trans hs
  refine ⟨L + p₀, ((integrable_haarMatrixTail μ (Nat.lt_succ_self (Module.finrank ℝ (Mat n n)))).const_mul
    (C ^ M * D ^ j)).mono' ?_ (ae_of_all _ fun g => ?_)⟩
  · have hδ : Continuous (fun g : G n => realNormalizedAbs g.val.det) := by
      unfold realNormalizedAbs
      exact Units.continuous_val.matrix_det.abs
    have hN : Continuous (fun g : G n => matrixDecay (L + p₀) g.val) := by
      unfold matrixDecay
      apply ((continuous_const.add Units.continuous_val.norm).pow (L + p₀)).inv₀
      intro g
      change (1 + ‖g.val‖) ^ (L + p₀) ≠ 0
      positivity
    exact (((continuous_realMatrixHeight (m := n)).pow M).mul
      (hδ.rpow_const (fun _ => Or.inr hs₀)) |>.mul hN).aestronglyMeasurable
  · let δ := realNormalizedAbs g.val.det
    let S := 1 + ‖g.val‖
    have hS : 1 ≤ S := le_add_of_nonneg_right (norm_nonneg _)
    have hS₀ : 0 < S := zero_lt_one.trans_le hS
    have hH : 0 ≤ H g := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos r) g)
    have hδ : 0 < δ := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
    have hδb : δ ≤ D * S ^ n := by
      have h := Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos r) g.val S
        (fun i j => (norm_entry_le_opNorm g.val i j).trans (le_add_of_nonneg_left zero_le_one))
      simpa only [δ, realNormalizedAbs, Real.norm_eq_abs] using h
    have hτb : δ ^ τ ≤ D ^ j * S ^ (n * j) := by
      calc
        _ ≤ (D * S ^ n) ^ τ := Real.rpow_le_rpow hδ.le hδb hτ
        _ ≤ (D * S ^ n) ^ (j : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hS)) hj
        _ = _ := by rw [Real.rpow_natCast, mul_pow, ← pow_mul S n j]
    have hHb : (H g * δ ^ 2) ^ M ≤ C ^ M * S ^ (2 * (n + 1) * M) := by
      rw [pow_mul, ← mul_pow]
      have h := Langlands.GodementJacquet.realMatrixHeight_mul_absDet_sq_bound (r := r) g
      apply pow_le_pow_left₀ (mul_nonneg hH (sq_nonneg _))
      simpa only [C, S, n, δ, realNormalizedAbs, Nat.cast_add, Nat.cast_one] using h
    have he : δ ^ s = (δ ^ 2) ^ M * δ ^ τ * δ ^ n := by
      rw [← pow_mul, ← Real.rpow_natCast δ (2 * M), ← Real.rpow_natCast δ n, ← Real.rpow_add hδ,
        ← Real.rpow_add hδ]
      congr 1
      dsimp only [τ]
      push_cast
      ring
    have hp : (H g * δ ^ 2) ^ M * δ ^ τ ≤ (C ^ M * D ^ j) * S ^ L := by
      refine (mul_le_mul hHb hτb (Real.rpow_nonneg hδ.le _) (by positivity)).trans_eq ?_
      dsimp only [L]
      rw [pow_add]
      ring
    change ‖H g ^ M * δ ^ s * (S ^ (L + p₀))⁻¹‖ ≤ (C ^ M * D ^ j) * (δ ^ n * (S ^ p₀)⁻¹)
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ = (H g * δ ^ 2) ^ M * δ ^ τ * δ ^ n * (S ^ (L + p₀))⁻¹ := by rw [he, mul_pow]; ring
      _ ≤ (C ^ M * D ^ j) * S ^ L * δ ^ n * (S ^ (L + p₀))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = _ := by rw [pow_add]; field_simp; ring

end Langlands.Global.RankinSelbergGlobal.RealGapLeadingSchwartz
