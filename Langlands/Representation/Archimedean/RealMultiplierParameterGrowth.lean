import Langlands.Representation.Archimedean.RealBlockMultiplierNormalization
import Mathlib.Analysis.Complex.Liouville

/-! # Uniform polynomial growth of real block multipliers on parameter disks -/

noncomputable section

open Set Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealBlockMultiplier

private theorem factor_norm_le {ε : ℤ} (hε : 0 ≤ ε) {ν : ℂ} {m d : ℕ}
    (hm : ‖ν‖ ≤ m) (hd : 2 * ‖ν‖ ≤ d) :
    ‖((ε : ℂ) + 2 * m + 1 - ν) / ((ε : ℂ) + 2 * m + 1 + ν)‖ ≤
      (((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ d := by
  let a := (ε : ℂ) + 2 * m + 1
  have hε' : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  have hreal : ‖a‖ = (ε : ℝ) + 2 * (m : ℝ) + 1 := by
    have he : a = ((ε : ℝ) + 2 * (m : ℝ) + 1 : ℝ) := by
      push_cast
      rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hden : (m : ℝ) + 1 ≤ ‖a + ν‖ := by
    have h := norm_sub_le (a + ν) ν
    rw [add_sub_cancel_right, hreal] at h
    linarith
  have hden₀ : 0 < ‖a + ν‖ := (by positivity : 0 < (m : ℝ) + 1).trans_le hden
  have hnum : ‖a - ν‖ ≤ ‖a + ν‖ + 2 * ‖ν‖ := by
    calc
      ‖a - ν‖ = ‖(a + ν) - 2 * ν‖ := by congr 1; ring
      _ ≤ ‖a + ν‖ + ‖2 * ν‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul]; norm_num
  have hstep : 2 * ‖ν‖ ≤ ((d : ℝ) / ((m : ℝ) + 1)) * ‖a + ν‖ := by
    calc
      _ ≤ (d : ℝ) := hd
      _ = ((d : ℝ) / ((m : ℝ) + 1)) * ((m : ℝ) + 1) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  change ‖(a - ν) / (a + ν)‖ ≤ _
  calc
    _ ≤ 1 + (d : ℝ) / ((m : ℝ) + 1) := by
      rw [norm_div, div_le_iff₀ hden₀, add_mul, one_mul]
      exact hnum.trans (by linarith only [hstep])
    _ ≤ (1 + 1 / ((m : ℝ) + 1)) ^ d := by
      rw [div_eq_mul_inv (d : ℝ), one_div]
      have h : 0 ≤ (((m : ℝ) + 1)⁻¹) := by positivity
      exact one_add_mul_le_pow (by linarith only [h]) d
    _ = _ := by
      congr 1
      field_simp
      ring

private theorem exists_uniform_seq_bound {ε : ℤ} (hε : 0 ≤ ε) (Q : Set ℂ) (hQ : IsCompact Q)
    (f : ℂ → ℕ → ℂ) (hc : ∀ m, ContinuousOn (fun z => f z m) Q)
    (l : ℕ) (hrec : ∀ z ∈ Q, ∀ m, l ≤ m →
      f z (m + 1) = f z m * (((ε : ℂ) + 2 * m + 1 - z) / ((ε : ℂ) + 2 * m + 1 + z))) :
    ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧ ∀ z ∈ Q, ∀ m : ℕ, ‖f z m‖ ≤ B * ((m : ℝ) + 1) ^ d := by
  classical
  obtain ⟨R, hR⟩ := hQ.exists_bound_of_continuousOn continuous_id.continuousOn
  obtain ⟨L, hL⟩ := exists_nat_ge R
  obtain ⟨d, hd⟩ := exists_nat_ge (2 * R)
  let N := max l L
  choose A hA using fun i : Fin (N + 1) => hQ.exists_bound_of_continuousOn (hc i.val)
  let B := ∑ i : Fin (N + 1), max 0 (A i)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => le_max_left _ _
  refine ⟨B, d, hB, fun z hz m => ?_⟩
  have hsmall (j : ℕ) (hj : j ≤ N) : ‖f z j‖ ≤ B * ((j : ℝ) + 1) ^ d := by
    let i : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hi : A i ≤ B := (le_max_right _ _).trans
      (Finset.single_le_sum (fun k _ => le_max_left (0 : ℝ) (A k)) (Finset.mem_univ i))
    have hp : 1 ≤ ((j : ℝ) + 1) ^ d :=
      one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) j])
    exact (hA i z hz).trans (hi.trans (le_mul_of_one_le_right hB hp))
  induction m with
  | zero => exact hsmall 0 (Nat.zero_le N)
  | succ m ih =>
    by_cases hm : m < N
    · exact hsmall (m + 1) (Nat.succ_le_of_lt hm)
    · have hm' : N ≤ m := Nat.le_of_not_gt hm
      have hlm : l ≤ m := (le_max_left _ _).trans hm'
      have hLm : L ≤ m := (le_max_right _ _).trans hm'
      have hz₁ : ‖z‖ ≤ (m : ℝ) := (hR z hz).trans (hL.trans (by exact_mod_cast hLm))
      have hz₂ : 2 * ‖z‖ ≤ (d : ℝ) := (mul_le_mul_of_nonneg_left (hR z hz) (by norm_num)).trans hd
      rw [hrec z hz m hlm, norm_mul]
      calc
        _ ≤ (B * ((m : ℝ) + 1) ^ d) * ((((m : ℝ) + 2) / ((m : ℝ) + 1)) ^ d) :=
          mul_le_mul ih (factor_norm_le hε hz₁ hz₂) (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          rw [mul_div, mul_comm ((m : ℝ) + 1), mul_div_cancel_right₀ _ (by positivity : (m : ℝ) + 1 ≠ 0)]
          push_cast
          ring

/-- On a compact parameter set avoiding the denominator roots, the generic sequence has a
single polynomial bound valid at every parameter and every mode. -/
theorem exists_uniform_genericSeq_bound {ε : ℤ} (hε : 0 ≤ ε) {Q : Set ℂ} (hQ : IsCompact Q)
    (hden : ∀ z ∈ Q, ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + z ≠ 0) :
    ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧
      ∀ z ∈ Q, ∀ m : ℕ, ‖genericSeq z ε m‖ ≤ B * ((m : ℝ) + 1) ^ d := by
  refine exists_uniform_seq_bound hε Q hQ (fun z m => genericSeq z ε m) ?_ 0 ?_
  · intro m z hz
    exact (analyticAt_genericSeq ε m (fun i _ => hden z hz i)).continuousAt.continuousWithinAt
  · intro z _ m _
    unfold genericSeq
    rw [Finset.prod_range_succ]

/-- After removing one specified denominator factor, the regularized sequence obeys the same
uniform polynomial conclusion on compact sets avoiding the remaining roots. -/
theorem exists_uniform_regularizedSeq_bound {ε : ℤ} (hε : 0 ≤ ε) (r : ℕ)
    {Q : Set ℂ} (hQ : IsCompact Q)
    (hden : ∀ z ∈ Q, ∀ i : ℕ, i ≠ r → (ε : ℂ) + 2 * i + 1 + z ≠ 0) :
    ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧
      ∀ z ∈ Q, ∀ m : ℕ, ‖regularizedSeq z ε r m‖ ≤ B * ((m : ℝ) + 1) ^ d := by
  refine exists_uniform_seq_bound hε Q hQ (fun z m => regularizedSeq z ε r m) ?_ (r + 1) ?_
  · intro m z hz
    exact (analyticAt_regularizedSeq ε r m
      (fun i _ hi => hden z hz i hi)).continuousAt.continuousWithinAt
  · intro z _ m hm
    have hrm : r < m := hm
    have hrm' : r < m + 1 := by omega
    have hne : m ≠ r := by omega
    have hmem : m ∉ (Finset.range m).erase r := by simp
    simp only [regularizedSeq, hrm, hrm', ↓reduceIte, Finset.range_add_one, Finset.erase_insert_of_ne hne,
      Finset.prod_insert hmem]
    ring

private theorem derivatives_of_uniform_bound {f : ℂ → ℕ → ℂ} {c : ℂ} {r B : ℝ} {d : ℕ}
    (hr : 0 < r) (ha : ∀ z ∈ closedBall c r, ∀ m : ℕ, AnalyticAt ℂ (fun w => f w m) z)
    (hB : ∀ z ∈ closedBall c r, ∀ m : ℕ, ‖f z m‖ ≤ B * ((m : ℝ) + 1) ^ d) :
    ∀ j m : ℕ, ‖iteratedDeriv j (fun w => f w m) c‖ ≤
      ((j.factorial : ℝ) * B / r ^ j) * ((m : ℝ) + 1) ^ d := by
  intro j m
  have hdiff : DiffContOnCl ℂ (fun w => f w m) (ball c r) := by
    constructor
    · intro z hz
      exact (ha z (ball_subset_closedBall hz) m).differentiableAt.differentiableWithinAt
    · intro z hz
      exact (ha z (closure_ball_subset_closedBall hz) m).continuousAt.continuousWithinAt
  refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr hdiff
    (fun z hz => hB z (sphere_subset_closedBall hz) m)).trans_eq ?_
  ring

/-- The uniform polynomial bounds include each parameter derivative at the center of the disk.
The degree can be held fixed when the derivative order varies. -/
def RealMultiplierParameterGrowthStatement : Prop :=
  ∀ (ε : ℤ), 0 ≤ ε → ∀ (c : ℂ) (r : ℝ), 0 < r →
    ((∀ z ∈ closedBall c r, ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + z ≠ 0) →
      ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧ ∀ j m : ℕ,
        ‖iteratedDeriv j (fun z => genericSeq z ε m) c‖ ≤
          ((j.factorial : ℝ) * B / r ^ j) * ((m : ℝ) + 1) ^ d) ∧
    ∀ l : ℕ, (∀ z ∈ closedBall c r, ∀ i : ℕ,
        i ≠ l → (ε : ℂ) + 2 * i + 1 + z ≠ 0) →
      ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧ ∀ j m : ℕ,
        ‖iteratedDeriv j (fun z => regularizedSeq z ε l m) c‖ ≤
          ((j.factorial : ℝ) * B / r ^ j) * ((m : ℝ) + 1) ^ d

theorem realMultiplierParameterGrowth : RealMultiplierParameterGrowthStatement := by
  intro ε hε c r hr
  constructor
  · intro hden
    obtain ⟨B, d, hB, hbound⟩ := exists_uniform_genericSeq_bound hε (isCompact_closedBall c r) hden
    exact ⟨B, d, hB, derivatives_of_uniform_bound hr
      (fun z hz m => analyticAt_genericSeq ε m (fun i _ => hden z hz i)) hbound⟩
  · intro l hden
    obtain ⟨B, d, hB, hbound⟩ := exists_uniform_regularizedSeq_bound hε l
      (isCompact_closedBall c r) hden
    exact ⟨B, d, hB, derivatives_of_uniform_bound hr
      (fun z hz m => analyticAt_regularizedSeq ε l m (fun i _ hi => hden z hz i hi)) hbound⟩

private theorem norm_iteratedDeriv_extend (ε : ℤ) (f : ℂ → ℕ → ℂ) (c : ℂ) (j : ℕ) (k : ℤ) :
    ‖iteratedDeriv j (fun z => extend ((-1 : ℂ) ^ ε.natAbs) (f z) k) c‖ =
      ‖iteratedDeriv j (fun z => f z (k.natAbs / 2)) c‖ := by
  by_cases hk : 0 ≤ k
  · simp only [extend, hk, ↓reduceIte]
  · simp only [extend, hk, ↓reduceIte, iteratedDeriv_const_mul_field, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]

private theorem derivative_extend_bound {f : ℂ → ℕ → ℂ} {c : ℂ} {d : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (ε : ℤ) (j : ℕ)
    (h : ∀ m : ℕ, ‖iteratedDeriv j (fun z => f z m) c‖ ≤ C * ((m : ℝ) + 1) ^ d)
    (k : ℤ) :
    ‖iteratedDeriv j (fun z => extend ((-1 : ℂ) ^ ε.natAbs) (f z) k) c‖ ≤
      C * ((k.natAbs : ℝ) + 1) ^ d := by
  rw [norm_iteratedDeriv_extend]
  refine (h _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ d) hC)
  apply add_le_add_left
  exact_mod_cast Nat.div_le_self k.natAbs 2

/-- On a disk without denominator roots, all parameter derivatives of the generic multiplier
have polynomial growth in the absolute integer mode, with a common degree. -/
theorem exists_genericMultiplier_derivative_bound {ε : ℤ} (hε : 0 ≤ ε) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hden : ∀ z ∈ closedBall c r, ∀ i : ℕ, (ε : ℂ) + 2 * i + 1 + z ≠ 0) :
    ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧ ∀ (j : ℕ) (k : ℤ),
      ‖iteratedDeriv j (fun z => genericMultiplier z ε k) c‖ ≤
        ((j.factorial : ℝ) * B / r ^ j) * ((k.natAbs : ℝ) + 1) ^ d := by
  obtain ⟨B, d, hB, h⟩ := (realMultiplierParameterGrowth ε hε c r hr).1 hden
  exact ⟨B, d, hB, fun j => derivative_extend_bound (by positivity) ε j (h j)⟩

/-- The same derivative bound holds for the regularized multiplier on disks without any of
the remaining denominator roots. -/
theorem exists_regularizedMultiplier_derivative_bound {ε : ℤ} (hε : 0 ≤ ε) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (l : ℕ)
    (hden : ∀ z ∈ closedBall c r, ∀ i : ℕ, i ≠ l → (ε : ℂ) + 2 * i + 1 + z ≠ 0) :
    ∃ (B : ℝ) (d : ℕ), 0 ≤ B ∧ ∀ (j : ℕ) (k : ℤ),
      ‖iteratedDeriv j (fun z => regularizedMultiplier z ε l k) c‖ ≤
        ((j.factorial : ℝ) * B / r ^ j) * ((k.natAbs : ℝ) + 1) ^ d := by
  obtain ⟨B, d, hB, h⟩ := (realMultiplierParameterGrowth ε hε c r hr).2 l hden
  exact ⟨B, d, hB, fun j => derivative_extend_bound (by positivity) ε j (h j)⟩

end Langlands.Archimedean.RealBlockMultiplier
