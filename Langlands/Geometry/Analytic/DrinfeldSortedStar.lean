import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! # Explicit inequalities for the thickening of the sorted-weight star polytope -/

noncomputable section

namespace Langlands.Analytic.NormClass

/-- In a sorted log-weight chamber, the width of the wraparound gap is `l - (v_last - v_0)`.
The inequalities require each adjacent gap to be at most this width. -/
def IsSortedStar {d : ℕ} (l : ℝ) (v : Fin (d + 1) → ℝ) : Prop :=
  Monotone v ∧ ∀ i : Fin d, v i.succ - v i.castSucc + (v (Fin.last d) - v 0) ≤ l

private theorem sub_le_steps {d : ℕ} {v : Fin (d + 1) → ℝ} {L : ℝ}
    (h : ∀ i : Fin d, v i.succ - v i.castSucc ≤ L) {i j : Fin (d + 1)} (hij : i ≤ j) :
    v j - v i ≤ ((j.val - i.val : ℕ) : ℝ) * L := by
  have hmono : Monotone (fun i : Fin (d + 1) => (i.val : ℝ) * L - v i) := by
    apply Fin.monotone_iff_le_succ.2
    intro k
    have hk := h k
    change (k.val : ℝ) * L - v k.castSucc ≤ ((k.val + 1 : ℕ) : ℝ) * L - v k.succ
    push_cast
    linarith
  have hh := hmono hij
  dsimp only at hh
  rw [Nat.cast_sub (show i.val ≤ j.val from hij)]
  linarith

/-- The finite linear tests on the log weights of a sorted point. -/
def sortedStarIneq {d : ℕ} (l ε : ℝ) (u : Fin (d + 1) → ℝ) (i j : Fin (d + 1)) : Prop :=
  let n : ℕ := j.val - i.val
  u j - u i + n * (u (Fin.last d) - u 0) < n * l + (1 + n) * ε

private theorem exists_star_in_band {d : ℕ} {l δ : ℝ} {u : Fin (d + 1) → ℝ}
    (hl : 0 < l) (hδ : 0 ≤ δ) (hu : Monotone u) (hs : u (Fin.last d) - u 0 < l)
    (hpair : ∀ i j : Fin (d + 1), u j - u i ≤
      δ + ((j.val - i.val : ℕ) : ℝ) * (l - (u (Fin.last d) - u 0) + δ)) :
    ∃ v : Fin (d + 1) → ℝ, IsSortedStar l v ∧ ∀ i, u i - δ ≤ v i ∧ v i ≤ u i := by
  by_cases hshort : u (Fin.last d) - u 0 ≤ δ
  · refine ⟨fun _ => u 0, ⟨monotone_const, fun i => ?_⟩, fun i => ?_⟩
    · simp [hl.le]
    · have hlast := hu (Fin.le_last i)
      exact ⟨by linarith, hu (Fin.zero_le i)⟩
  classical
  let L := l - (u (Fin.last d) - u 0) + δ
  have hL : 0 ≤ L := by dsimp [L]; linarith
  let U : Finset (Fin (d + 1)) := Finset.univ
  have hU : U.Nonempty := ⟨0, Finset.mem_univ _⟩
  let f (i j : Fin (d + 1)) := u j - δ - ((j.val - i.val : ℕ) : ℝ) * L
  let w (i : Fin (d + 1)) := U.sup' hU (f i)
  let v (i : Fin (d + 1)) := max (u 0) (w i)
  have hw (i j : Fin (d + 1)) : f i j ≤ w i := Finset.le_sup' _ (Finset.mem_univ j)
  have hb (i : Fin (d + 1)) : u i - δ ≤ v i ∧ v i ≤ u i := by
    constructor
    · have h := (hw i i).trans (le_max_right (u 0) (w i))
      simpa [f, v] using h
    · refine max_le (hu (Fin.zero_le i)) ((Finset.sup'_le_iff hU _).2 fun j _ => ?_)
      have h := hpair i j
      dsimp only [f]
      change u j - u i ≤ δ + ((j.val - i.val : ℕ) : ℝ) * L at h
      linarith
  have hv0 : v 0 = u 0 := le_antisymm (hb 0).2 (le_max_left _ _)
  have hvlast : v (Fin.last d) = u (Fin.last d) - δ := by
    refine le_antisymm (max_le (by linarith) ?_) (hb (Fin.last d)).1
    refine (Finset.sup'_le_iff hU _).2 fun j _ => ?_
    dsimp [f]
    have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
    simp only [Nat.sub_eq_zero_of_le hj, Nat.cast_zero, zero_mul, sub_zero]
    exact sub_le_sub_right (hu (Fin.le_last j)) δ
  have hwmono : Monotone w := by
    intro i j hij
    refine (Finset.sup'_le_iff hU _).2 fun k _ => ?_
    refine le_trans ?_ (hw j k)
    dsimp [f]
    have hsub : k.val - j.val ≤ k.val - i.val := Nat.sub_le_sub_left hij _
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) hL) _
  refine ⟨v, ⟨fun i j hij => max_le_max le_rfl (hwmono hij), fun i => ?_⟩, hb⟩
  have hstep : w i.succ ≤ w i.castSucc + L := by
    refine (Finset.sup'_le_iff hU _).2 fun j _ => ?_
    refine le_trans ?_ (add_le_add_left (hw i.castSucc j) L)
    have hsub : j.val - i.val ≤ j.val - (i.val + 1) + 1 := by omega
    have hcast : ((j.val - i.val : ℕ) : ℝ) ≤ ((j.val - (i.val + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hsub
    dsimp [f]
    linarith only [mul_le_mul_of_nonneg_right hcast hL]
  have hstep' : v i.succ ≤ v i.castSucc + L := max_le
    ((le_max_left _ _).trans (le_add_of_nonneg_right hL))
    (hstep.trans (add_le_add_left (le_max_right _ _) L))
  rw [hvlast, hv0]
  dsimp [L] at hstep'
  linarith

/-- On a sorted chamber of log-width `< l`, the open thickness condition is exactly the finite
family of strict `sortedStarIneq` tests. In particular its complement is a finite union of
closed linear conditions, without projecting any polyhedra. -/
theorem exists_isSortedStar_iff {d : ℕ} {l ε : ℝ} {u : Fin (d + 1) → ℝ}
    (hl : 0 < l) (hε : 0 < ε) (hu : Monotone u) (hs : u (Fin.last d) - u 0 < l) :
    (∃ v : Fin (d + 1) → ℝ, IsSortedStar l v ∧ ∀ i j, (u i - v i) - (u j - v j) < ε) ↔
      ∀ i j, i ≤ j → sortedStarIneq l ε u i j := by
  constructor
  · rintro ⟨v, hv, hdist⟩ i j hij
    have hj := hdist j i
    have hlast := hdist (Fin.last d) 0
    have hc : 0 ≤ ((j.val - i.val : ℕ) : ℝ) := by positivity
    have hB := sub_le_steps (v := v) (L := l - (v (Fin.last d) - v 0))
      (fun k => by have hk := hv.2 k; linarith) hij
    have h' : l - (v (Fin.last d) - v 0) ≤ l - (u (Fin.last d) - u 0) + ε := by linarith
    have hB' := hB.trans (mul_le_mul_of_nonneg_left h' hc)
    dsimp [sortedStarIneq]
    linarith
  · intro h
    classical
    let U : Finset (Fin (d + 1) × Fin (d + 1)) := Finset.univ
    have hU : U.Nonempty := ⟨(0, 0), Finset.mem_univ _⟩
    let s := u (Fin.last d) - u 0
    let f (p : Fin (d + 1) × Fin (d + 1)) :=
      let n : ℕ := p.2.val - p.1.val
      (u p.2 - u p.1 + n * (s - l)) / (1 + n)
    have hflt (p : Fin (d + 1) × Fin (d + 1)) : f p < ε := by
      rcases le_total p.1 p.2 with h12 | h21
      · have hp := h p.1 p.2 h12
        dsimp [f]
        rw [div_lt_iff₀ (by positivity)]
        dsimp [sortedStarIneq] at hp
        dsimp [s]
        linarith
      · have hzero := Nat.sub_eq_zero_of_le (show p.2.val ≤ p.1.val from h21)
        have hle := hu h21
        simp only [f, hzero, Nat.cast_zero, zero_mul, add_zero, div_one]
        linarith
    let δ := max 0 (U.sup' hU f)
    have hδ0 : 0 ≤ δ := le_max_left _ _
    have hδε : δ < ε := max_lt hε ((Finset.sup'_lt_iff hU).2 fun p _ => hflt p)
    have hpair (i j : Fin (d + 1)) : u j - u i ≤
        δ + ((j.val - i.val : ℕ) : ℝ) * (l - (u (Fin.last d) - u 0) + δ) := by
      have hp : f (i, j) ≤ δ := (Finset.le_sup' _ (Finset.mem_univ (i, j))).trans (le_max_right _ _)
      dsimp [f, s] at hp
      rw [div_le_iff₀ (by positivity)] at hp
      linarith
    obtain ⟨v, hv, hb⟩ := exists_star_in_band hl hδ0 hu hs hpair
    refine ⟨v, hv, fun i j => ?_⟩
    have hi := (hb i).1
    have hj := (hb j).2
    linarith

/-- Failure of a log-weight test is a closed monomial inequality in the original positive
weights. The powers are natural numbers, so these are analytic functions in applications. -/
theorem not_sortedStarIneq_log_iff {d : ℕ} {l ε : ℝ} {w : Fin (d + 1) → ℝ}
    (hw : ∀ i, 0 < w i) (i j : Fin (d + 1)) :
    ¬ sortedStarIneq l ε (fun k => Real.log (w k)) i j ↔
      let n : ℕ := j.val - i.val
      Real.exp (n * l + (1 + n) * ε) * (w i * w 0 ^ n) ≤ w j * w (Fin.last d) ^ n := by
  let n : ℕ := j.val - i.val
  change ¬ (Real.log (w j) - Real.log (w i) + (n : ℝ) *
      (Real.log (w (Fin.last d)) - Real.log (w 0)) < (n : ℝ) * l + (1 + n) * ε) ↔ _
  rw [not_lt, ← Real.exp_le_exp,
    Real.exp_add (Real.log (w j) - Real.log (w i)), Real.exp_sub, Real.exp_nat_mul,
    Real.exp_sub, Real.exp_log (hw _), Real.exp_log (hw _), Real.exp_log (hw _),
    Real.exp_log (hw _), div_pow, div_mul_div_comm,
    le_div_iff₀ (mul_pos (hw _) (pow_pos (hw _) _))]

end Langlands.Analytic.NormClass
