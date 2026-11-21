import Langlands.Representation.GodementJacquet.ComplexMatrixConvergence
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerFiniteGrowth

/-! # Schwartz domination of the leading rectangle in the complex gap recurrence -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingSchwartz

open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open ArchimedeanLocal (complexNormalizedAbs)
open Langlands.RankinSelberg.GLDeterminantDensity (matrixWeight)
open ComplexPlaceAnalytic (norm_entry_le_complexMatrixHeight two_le_complexMatrixHeight complexMatrixHeight_inv)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "H" => complexMatrixHeight

/-- Stack a leading square matrix and its lower rectangle along their rows. -/
def leadingStack {k d : ℕ} (A : Mat k k) (Y : Mat d k) : Mat (k + d) k :=
  fun i j => Fin.append (fun l => A l j) (fun l => Y l j) i

private theorem norm_leading_left {k d : ℕ} (A : Mat k k) (Y : Mat d k) :
    ‖A‖ ≤ ‖leadingStack A Y‖ := by
  refine (Matrix.norm_le_iff (norm_nonneg _)).mpr fun i j => ?_
  have h := Matrix.norm_entry_le_entrywise_sup_norm (leadingStack A Y) (i := i.castAdd d) (j := j)
  simpa only [leadingStack, Fin.append_left] using h

private theorem norm_leading_right {k d : ℕ} (A : Mat k k) (Y : Mat d k) :
    ‖Y‖ ≤ ‖leadingStack A Y‖ := by
  refine (Matrix.norm_le_iff (norm_nonneg _)).mpr fun i j => ?_
  have h := Matrix.norm_entry_le_entrywise_sup_norm (leadingStack A Y) (i := i.natAdd k) (j := j)
  simpa only [leadingStack, Fin.append_right] using h

private theorem norm_mul_le_rank {n k : ℕ} (A : Mat n n) (B : Mat n k) {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A * B‖ ≤ (n : ℝ) * C * ‖B‖ := by
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, C * ‖B‖ := by
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hA i l) (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) hC
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

/-- A Schwartz test on the stacked rectangle gives simultaneous polynomial decay in its
square and rectangular input, at the cost of a power of the height of the left multiplier. -/
def ComplexGapLeadingSchwartzStatement : Prop :=
  ∀ (k d : ℕ), 0 < k + d → ∀ (Φ : 𝓢(Mat (k + d) k, ℂ)) (p q : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G (k + d)) (A : Mat k k) (Y : Mat d k),
      ‖Φ (g.val * leadingStack A Y)‖ ≤ C * H g ^ (p + q) /
        ((1 + ‖A‖) ^ p * (1 + ‖Y‖) ^ q)

theorem complexGapLeadingSchwartz : ComplexGapLeadingSchwartzStatement := by
  intro k d hn Φ p q
  let n := k + d
  let m := p + q
  let S := (Finset.Iic (m, 0)).sup (schwartzSeminormFamily ℝ (Mat n k) ℂ) Φ
  have hS : 0 ≤ S := apply_nonneg _ _
  refine ⟨(2 : ℝ) ^ m * S * (n : ℝ) ^ m, by positivity, fun g A Y => ?_⟩
  let B := g.val * leadingStack A Y
  let L := (n : ℝ) * H g
  have hH : 1 ≤ H g := (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_complexMatrixHeight hn g)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hn) hH
  have hB : g⁻¹.val * B = leadingStack A Y := by
    dsimp only [B]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hNorm : ‖leadingStack A Y‖ ≤ L * ‖B‖ := by
    rw [← hB]
    apply norm_mul_le_rank _ _ (zero_le_one.trans hH)
    intro i j
    simpa only [complexMatrixHeight_inv] using norm_entry_le_complexMatrixHeight hn g⁻¹ i j
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

/-- Radial polynomial decay in the additive matrix space. -/
def matrixDecay {m n : ℕ} (p : ℕ) (X : Mat m n) : ℝ := ((1 + ‖X‖) ^ p)⁻¹

private theorem integrable_haarMatrixTail {n p : ℕ}
    (hp : Module.finrank ℝ (Mat n n) < p) :
    Integrable (fun g : G n => complexNormalizedAbs g.val.det ^ n * matrixDecay p g.val)
      (complexGeneralLinearHaar n) := by
  have hT : Integrable (matrixDecay p : Mat n n → ℝ) (matrixLebesgue n) := by
    refine (integrable_one_add_norm (μ := matrixLebesgue n) (r := (p : ℝ)) (by exact_mod_cast hp)).congr ?_
    exact ae_of_all _ fun X => by simp only [matrixDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖X‖),
      Real.rpow_natCast]
  let U := Set.range (Units.val : G n → Mat n n)
  have hU : MeasurableSet U := by
    have he : U = {X : Mat n n | X.det ≠ 0} := by
      ext X
      constructor
      · rintro ⟨g, rfl⟩
        exact Matrix.GeneralLinearGroup.det_ne_zero g
      · intro hX
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hX, rfl⟩
    rw [he]
    exact (isOpen_ne_fun continuous_id.matrix_det continuous_const).measurableSet
  let F (X : Mat n n) : ℂ := (complexNormalizedAbs X.det ^ n * matrixDecay p X : ℝ)
  have hF : Integrable (fun g : G n => F g.val) (complexGeneralLinearHaar n) := by
    apply (integrable_complexGeneralLinearHaar_iff F).mpr
    refine (hT.ofReal.mono_measure Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem hU] with X hX
    obtain ⟨g, rfl⟩ := hX
    have hδ : complexNormalizedAbs g.val.det ≠ 0 :=
      (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _).ne'
    change (matrixDecay p g.val : ℂ) = ((complexNormalizedAbs g.val.det)⁻¹ ^ n : ℝ) •
      ((complexNormalizedAbs g.val.det ^ n * matrixDecay p g.val : ℝ) : ℂ)
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hδ, one_pow, one_mul]
  refine hF.norm.congr (ae_of_all _ fun g => ?_)
  dsimp only [F]
  rw [Complex.norm_real, Real.norm_of_nonneg (by unfold matrixDecay complexNormalizedAbs; positivity)]

/-- One leading square factor of the joint kernel, with the height from the translated
small Whittaker vector and an independently chosen determinant power. -/
def weightedMatrixTail {n : ℕ} (M p : ℕ) (s : ℝ) (g : G n) : ℝ :=
  H g ^ M * complexNormalizedAbs g.val.det ^ s * matrixDecay p g.val

/-- The square factor is Haar integrable at any sufficiently large real determinant power
with a sufficiently large additive matrix decay order. -/
theorem exists_integrable_weightedMatrixTail (r M : ℕ) (s : ℝ) (hs : (r + 1 : ℕ) + (M : ℝ) ≤ s) :
    ∃ p : ℕ, Integrable (weightedMatrixTail M p s) (complexGeneralLinearHaar (r + 1)) := by
  let n := r + 1
  let p₀ := Module.finrank ℝ (Mat n n) + 1
  let τ := s - (n : ℝ) - (M : ℝ)
  have hτ : 0 ≤ τ := by dsimp only [τ, n]; linarith
  obtain ⟨j, hj⟩ := exists_nat_ge τ
  let L := 2 * (n + 1) * M + 2 * n * j
  let C := 2 * (n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2
  let D := (n.factorial : ℝ) ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 1 ≤ D := one_le_pow₀ (by exact_mod_cast Nat.factorial_pos n)
  have hs₀ : 0 ≤ s := (by positivity : 0 ≤ (r + 1 : ℕ) + (M : ℝ)).trans hs
  refine ⟨L + p₀, ((integrable_haarMatrixTail (Nat.lt_succ_self (Module.finrank ℝ (Mat n n)))).const_mul
    (C ^ M * D ^ j)).mono' ?_ (ae_of_all _ fun g => ?_)⟩
  · have hδ : Continuous (fun g : G n => complexNormalizedAbs g.val.det) := by
      unfold complexNormalizedAbs
      exact (Units.continuous_val.matrix_det.norm).pow 2
    have hN : Continuous (fun g : G n => matrixDecay (L + p₀) g.val) := by
      unfold matrixDecay
      apply ((continuous_const.add Units.continuous_val.norm).pow (L + p₀)).inv₀
      intro g
      change (1 + ‖g.val‖) ^ (L + p₀) ≠ 0
      positivity
    exact (((continuous_complexMatrixHeight (r := r)).pow M).mul
      (hδ.rpow_const (fun _ => Or.inr hs₀)) |>.mul hN).aestronglyMeasurable
  · let δ := complexNormalizedAbs g.val.det
    let S := 1 + ‖g.val‖
    have hS : 1 ≤ S := le_add_of_nonneg_right (norm_nonneg _)
    have hS₀ : 0 < S := zero_lt_one.trans_le hS
    have hH : 0 ≤ H g := zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)
    have hδ : 0 < δ := pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _
    have hδb : δ ≤ D * S ^ (2 * n) := by
      have h := Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos r) g.val S
        (fun i j => (Matrix.norm_entry_le_entrywise_sup_norm g.val).trans (le_add_of_nonneg_left zero_le_one))
      change ‖g.val.det‖ ^ 2 ≤ D * S ^ (2 * n)
      rw [Nat.mul_comm 2 n, pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h _
    have hτb : δ ^ τ ≤ D ^ j * S ^ (2 * n * j) := by
      calc
        _ ≤ (D * S ^ (2 * n)) ^ τ := Real.rpow_le_rpow hδ.le hδb hτ
        _ ≤ (D * S ^ (2 * n)) ^ (j : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hS)) hj
        _ = _ := by rw [Real.rpow_natCast, mul_pow, ← pow_mul S (2 * n) j]
    have hHb : (H g * δ) ^ M ≤ C ^ M * S ^ (2 * (n + 1) * M) := by
      rw [pow_mul, ← mul_pow]
      have h := Langlands.GodementJacquet.complexMatrixHeight_mul_det_bound g
      apply pow_le_pow_left₀ (mul_nonneg hH hδ.le)
      simpa only [C, S, n, Nat.cast_add, Nat.cast_one] using h
    have he : δ ^ s = δ ^ M * δ ^ τ * δ ^ n := by
      rw [← Real.rpow_natCast δ M, ← Real.rpow_natCast δ n, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
      dsimp only [τ]
      ring
    have hp : (H g * δ) ^ M * δ ^ τ ≤ (C ^ M * D ^ j) * S ^ L := by
      refine (mul_le_mul hHb hτb (Real.rpow_nonneg hδ.le _) (by positivity)).trans_eq ?_
      dsimp only [L]
      rw [pow_add]
      ring
    change ‖H g ^ M * δ ^ s * (S ^ (L + p₀))⁻¹‖ ≤ (C ^ M * D ^ j) * (δ ^ n * (S ^ p₀)⁻¹)
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ = (H g * δ) ^ M * δ ^ τ * δ ^ n * (S ^ (L + p₀))⁻¹ := by rw [he, mul_pow]; ring
      _ ≤ (C ^ M * D ^ j) * S ^ L * δ ^ n * (S ^ (L + p₀))⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = _ := by rw [pow_add]; field_simp; ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapLeadingSchwartz
