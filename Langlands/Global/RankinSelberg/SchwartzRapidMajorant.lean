import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Schwartz majorants from rapid bounds -/

noncomputable section
open scoped Classical ContDiff
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace SchwartzMajorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Absolute summability in every Schwartz seminorm gives a pointwise series
which is again a Schwartz function. -/
theorem exists_schwartz_tsum [CompleteSpace G] (f : ℕ → SchwartzMap E G)
    (hf : ∀ k n : ℕ, Summable (fun j => SchwartzMap.seminorm ℝ k n (f j))) :
    ∃ Φ : SchwartzMap E G, ∀ x, Φ x = ∑' j, f j x := by
  have hder : ∀ n j x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤
      SchwartzMap.seminorm ℝ 0 n (f j) :=
    fun n j x => (f j).norm_iteratedFDeriv_le_seminorm ℝ n x
  have hsmooth : ContDiff ℝ ∞ (fun x => ∑' j, f j x) :=
    contDiff_tsum (fun j => (f j).smooth ⊤)
      (fun n _ => hf 0 n) (fun n j x _ => hder n j x)
  refine ⟨⟨fun x => ∑' j, f j x, hsmooth, ?_⟩, fun _ => rfl⟩
  intro k n
  refine ⟨∑' j, SchwartzMap.seminorm ℝ k n (f j), fun x => ?_⟩
  have hsum : Summable (fun j => ‖iteratedFDeriv ℝ n (f j) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hder n · x) (hf 0 n)
  rw [iteratedFDeriv_tsum_apply (fun j => (f j).smooth ⊤)
    (fun m _ => hf 0 m) (fun m j y _ => hder m j y) (by exact le_top) x]
  calc
    ‖x‖ ^ k * ‖∑' j, iteratedFDeriv ℝ n (f j) x‖ ≤
        ‖x‖ ^ k * ∑' j, ‖iteratedFDeriv ℝ n (f j) x‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) (by positivity)
    _ = ∑' j, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f j) x‖ :=
      (hsum.tsum_mul_left _).symm
    _ ≤ _ := (hsum.mul_left _).tsum_le_tsum
      (fun j => (f j).le_seminorm ℝ k n x) (hf k n)

/-- Dilating a Schwartz function by a radius at least one costs at most its
`k`th power in the seminorm of weight `k`, uniformly in derivative order. -/
theorem dilation_decay_le (f : SchwartzMap E G) {R : ℝ} (hR : 1 ≤ R)
    (k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (R⁻¹ • y)) x‖ ≤
      R ^ k * SchwartzMap.seminorm ℝ k n f := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRi : 0 ≤ R⁻¹ := (inv_pos.mpr hR0).le
  have hRi1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hx : ‖x‖ = R * ‖R⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hRi, ← mul_assoc,
      mul_inv_cancel₀ hR0.ne', one_mul]
  rw [iteratedFDeriv_comp_const_smul R⁻¹ (f.smooth n), norm_smul,
    norm_pow, Real.norm_eq_abs, abs_of_nonneg hRi]
  calc
    ‖x‖ ^ k * (R⁻¹ ^ n * ‖iteratedFDeriv ℝ n f (R⁻¹ • x)‖) ≤
        ‖x‖ ^ k * (1 * ‖iteratedFDeriv ℝ n f (R⁻¹ • x)‖) := by
      gcongr
      exact pow_le_one₀ hRi hRi1
    _ = R ^ k * (‖R⁻¹ • x‖ ^ k *
        ‖iteratedFDeriv ℝ n f (R⁻¹ • x)‖) := by rw [hx, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (f.le_seminorm ℝ k n _) (by positivity)

/-- A dilation of a Schwartz function by a radius at least one. -/
def dilate (f : SchwartzMap E G) (R : ℝ) (hR : 1 ≤ R) : SchwartzMap E G where
  toFun x := f (R⁻¹ • x)
  smooth' := (f.smooth ⊤).comp (contDiff_id.const_smul R⁻¹)
  decay' k n := ⟨R ^ k * SchwartzMap.seminorm ℝ k n f,
    dilation_decay_le f hR k n⟩

theorem seminorm_dilate_le (f : SchwartzMap E G) (R : ℝ) (hR : 1 ≤ R)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (dilate f R hR) ≤
      R ^ k * SchwartzMap.seminorm ℝ k n f :=
  (dilate f R hR).seminorm_le_bound ℝ k n (by positivity)
    (dilation_decay_le f hR k n)

omit [NormedSpace ℝ E] in
/-- Rapid polynomial bounds give nonnegative tail coefficients with summable
dyadic weighted moments. -/
theorem exists_tail_coefficients {I : Type*} (z : I → E) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hrapid : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ i, (1 + ‖z i‖) ^ N * w i ≤ B) :
    ∃ a : ℕ → ℝ, (∀ j, 0 ≤ a j) ∧
      (∀ i j, (2 : ℝ) ^ j ≤ 1 + ‖z i‖ → w i ≤ a j) ∧
      (∀ k : ℕ, Summable (fun j => a j * ((2 : ℝ) ^ (j + 1)) ^ k)) := by
  let S (j : ℕ) : Set ℝ :=
    insert 0 (w '' {i | (2 : ℝ) ^ j ≤ 1 + ‖z i‖})
  have hSne (j : ℕ) : (S j).Nonempty := ⟨0, Set.mem_insert _ _⟩
  have hupper (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
      (hbound : ∀ i, (1 + ‖z i‖) ^ N * w i ≤ B)
      (j : ℕ) : ∀ y ∈ S j, y ≤ B / ((2 : ℝ) ^ j) ^ N := by
    intro y hy
    rcases hy with rfl | ⟨i, hi, rfl⟩
    · positivity
    · apply (le_div_iff₀ (by positivity)).mpr
      calc
        w i * ((2 : ℝ) ^ j) ^ N = ((2 : ℝ) ^ j) ^ N * w i := mul_comm _ _
        _ ≤ (1 + ‖z i‖) ^ N * w i :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hi N) (hw i)
        _ ≤ B := hbound i
  obtain ⟨B₀, hB₀, hbound₀⟩ := hrapid 0
  have hSbdd (j : ℕ) : BddAbove (S j) :=
    ⟨B₀ / ((2 : ℝ) ^ j) ^ 0, hupper 0 hB₀ hbound₀ j⟩
  let a : ℕ → ℝ := fun j => sSup (S j)
  have ha (j : ℕ) : 0 ≤ a j := le_csSup (hSbdd j) (Set.mem_insert _ _)
  refine ⟨a, ha, fun i j hij =>
    le_csSup (hSbdd j) (Set.mem_insert_of_mem _ ⟨i, hij, rfl⟩), ?_⟩
  intro k
  obtain ⟨B, hB, hbound⟩ := hrapid (k + 1)
  have hcoef (j : ℕ) : a j ≤ B / ((2 : ℝ) ^ j) ^ (k + 1) :=
    csSup_le (hSne j) (hupper (k + 1) hB hbound j)
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (ha j) (by positivity)) (fun j => ?_)
    (summable_geometric_two.mul_left (B * (2 : ℝ) ^ k))
  calc
    a j * ((2 : ℝ) ^ (j + 1)) ^ k ≤
        (B / ((2 : ℝ) ^ j) ^ (k + 1)) * ((2 : ℝ) ^ (j + 1)) ^ k :=
      mul_le_mul_of_nonneg_right (hcoef j) (by positivity)
    _ = (B * (2 : ℝ) ^ k) * ((1 : ℝ) / 2) ^ j := by
      rw [pow_succ (2 : ℝ) j, mul_pow, pow_succ, div_pow, one_pow]
      field_simp

/-- A prescribed nonnegative Schwartz bump produces a majorant. Any equality
preserved by all its dilations is preserved by the resulting majorant. -/
theorem exists_nonneg_schwartz_majorant_of_bump
    (b : SchwartzMap E ℝ) (hbnon : ∀ x, 0 ≤ b x)
    (hbone : ∀ x, ‖x‖ ≤ 1 → b x = 1)
    {I : Type*} (z : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hrapid : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ i, (1 + ‖z i‖) ^ N * w i ≤ B) :
    ∃ Φ : SchwartzMap E ℝ, (∀ x, 0 ≤ Φ x) ∧ (∀ i, w i ≤ Φ (z i)) ∧
      ∀ x y, (∀ R : ℝ, 1 ≤ R → b (R⁻¹ • x) = b (R⁻¹ • y)) → Φ x = Φ y := by
  obtain ⟨a, ha, htail, hsum⟩ := exists_tail_coefficients z w hw hrapid
  let R (j : ℕ) : ℝ := 2 ^ (j + 1)
  have hR (j : ℕ) : 1 ≤ R j := one_le_pow₀ (by norm_num)
  have hRpos (j : ℕ) : 0 < R j := lt_of_lt_of_le zero_lt_one (hR j)
  let f (j : ℕ) : SchwartzMap E ℝ := a j • dilate b (R j) (hR j)
  have hnon (j : ℕ) (x : E) : 0 ≤ f j x :=
    mul_nonneg (ha j) (hbnon _)
  have hseminorm (k n : ℕ) :
      Summable (fun j => SchwartzMap.seminorm ℝ k n (f j)) := by
    refine Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) (fun j => ?_)
      ((hsum k).mul_right (SchwartzMap.seminorm ℝ k n b))
    change SchwartzMap.seminorm ℝ k n (a j • dilate b (R j) (hR j)) ≤ _
    rw [map_smul_eq_mul, Real.norm_of_nonneg (ha j)]
    calc
      a j * SchwartzMap.seminorm ℝ k n (dilate b (R j) (hR j)) ≤
          a j * (R j ^ k * SchwartzMap.seminorm ℝ k n b) :=
        mul_le_mul_of_nonneg_left (seminorm_dilate_le b _ _ k n) (ha j)
      _ = _ := by ring
  obtain ⟨Φ, hΦ⟩ := exists_schwartz_tsum f hseminorm
  have hpoint (x : E) : Summable (fun j => f j x) := by
    refine summable_norm_iff.mp (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => (f j).norm_le_seminorm ℝ x) (hseminorm 0 0))
  refine ⟨Φ, fun x => by rw [hΦ]; exact tsum_nonneg (hnon · x), ?_, ?_⟩
  swap
  · intro x y hxy
    rw [hΦ, hΦ]
    apply tsum_congr
    intro j
    change a j * b ((R j)⁻¹ • x) = a j * b ((R j)⁻¹ • y)
    rw [hxy (R j) (hR j)]
  intro i
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near
    (show 1 ≤ 1 + ‖z i‖ from le_add_of_nonneg_right (norm_nonneg _))
    (show (1 : ℝ) < 2 by norm_num)
  have hz : ‖z i‖ ≤ R j := (by linarith : ‖z i‖ ≤ 1 + ‖z i‖).trans hj'.le
  have hb : b ((R j)⁻¹ • z i) = 1 := by
    apply hbone
    simpa only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hRpos j)), ← div_eq_inv_mul] using
      (div_le_one (hRpos j)).mpr hz
  have hterm : f j (z i) = a j := by
    change a j * b ((R j)⁻¹ • z i) = a j
    rw [hb, mul_one]
  calc
    w i ≤ a j := htail i j hj
    _ = f j (z i) := hterm.symm
    _ ≤ ∑' l, f l (z i) := by
      simpa using (hpoint (z i)).sum_le_tsum ({j} : Finset ℕ) (fun l _ => hnon l (z i))
    _ = Φ (z i) := (hΦ _).symm

/-- Any nonnegative family with uniform rapid bounds along its parameter
points admits a nonnegative real Schwartz majorant. No regularity of the
family or its supremum is assumed. -/
theorem exists_nonneg_schwartz_majorant [FiniteDimensional ℝ E]
    {I : Type*} (z : I → E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hrapid : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ i, (1 + ‖z i‖) ^ N * w i ≤ B) :
    ∃ Φ : SchwartzMap E ℝ, (∀ x, 0 ≤ Φ x) ∧ ∀ i, w i ≤ Φ (z i) := by
  let b₀ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let b : SchwartzMap E ℝ := b₀.hasCompactSupport.toSchwartzMap b₀.contDiff
  obtain ⟨Φ, hnon, hbound, -⟩ := exists_nonneg_schwartz_majorant_of_bump b
    (fun x => b₀.nonneg' x)
    (fun x hx => b₀.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using hx))
    z w hw hrapid
  exact ⟨Φ, hnon, hbound⟩

end SchwartzMajorant

end Langlands.Global.RankinSelbergGlobal
