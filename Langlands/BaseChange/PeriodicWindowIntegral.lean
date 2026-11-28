import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals over a window of a periodic level function

Let `G` be a group with a left-invariant measure `μ`, `a : G → ℤ` an additive level function
(`a (g * h) = a g + a h`) and `z ∈ G` with `a z = m`. For a function `Φ` with
`Φ (z * g) = Φ g`, the integral of `Φ` over the window `{g | k ≤ a g < k + m}` does not depend
on `k`, provided `Φ` is integrable on every level set `{g | a g = j}`. Consequently the window
integral `∫_{0 ≤ a < m} Φ` is invariant under every left translation of `Φ`
(`integral_window_comp_mul_left`).

For `G = GL_n(F)`, `a = ord ∘ det` and `z` the scalar uniformizer, the window
`{0 ≤ ord det < n}` is a fundamental domain for the action of `z^ℤ`, and the window integral
replaces the integral over `z^ℤ \ G`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange.PeriodicWindow

variable {G : Type*} {E : Type*} [NormedAddCommGroup E]

/-- The level set `{g | a g = j}`. -/
def levelSet (a : G → ℤ) (j : ℤ) : Set G := {g | a g = j}

/-- The window `{g | k ≤ a g < k + m}`. -/
def window (a : G → ℤ) (m : ℕ) (k : ℤ) : Set G := {g | k ≤ a g ∧ a g < k + m}

theorem mem_levelSet {a : G → ℤ} {j : ℤ} {g : G} : g ∈ levelSet a j ↔ a g = j := Iff.rfl

theorem mem_window {a : G → ℤ} {m : ℕ} {k : ℤ} {g : G} :
    g ∈ window a m k ↔ k ≤ a g ∧ a g < k + m := Iff.rfl

/-- The window indicator is the sum of the `m` level-set indicators it contains. -/
theorem window_indicator_eq_sum (a : G → ℤ) (m : ℕ) (k : ℤ) (Φ : G → E) (g : G) :
    (window a m k).indicator Φ g =
      ∑ i ∈ Finset.range m, (levelSet a (k + i)).indicator Φ g := by
  classical
  by_cases hg : g ∈ window a m k
  · rw [Set.indicator_of_mem hg]
    obtain ⟨h₁, h₂⟩ := hg
    have hi : ((a g - k).toNat : ℤ) = a g - k := Int.toNat_of_nonneg (by omega)
    rw [Finset.sum_eq_single (a g - k).toNat]
    · rw [Set.indicator_of_mem]
      change a g = k + ((a g - k).toNat : ℤ)
      omega
    · intro i _ hik
      rw [Set.indicator_of_notMem]
      change ¬ a g = k + (i : ℤ)
      omega
    · intro hm
      exfalso
      apply hm
      rw [Finset.mem_range]
      omega
  · rw [Set.indicator_of_notMem hg]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Set.indicator_of_notMem]
    intro hgi
    apply hg
    change a g = k + (i : ℤ) at hgi
    rw [Finset.mem_range] at hi
    exact ⟨by omega, by omega⟩

/-- An `m`-periodic sequence has the same sum over any `m` consecutive indices. -/
theorem sum_range_shift_of_periodic {m : ℕ} (c : ℤ → E) (hc : ∀ j, c (j + m) = c j) (k : ℤ) :
    ∑ i ∈ Finset.range m, c (k + i) = ∑ i ∈ Finset.range m, c i := by
  have hstep : ∀ k : ℤ, ∑ i ∈ Finset.range m, c (k + 1 + i) =
      ∑ i ∈ Finset.range m, c (k + i) := by
    intro k
    have h₁ := Finset.sum_range_succ (fun i : ℕ => c (k + i)) m
    have h₂ := Finset.sum_range_succ' (fun i : ℕ => c (k + i)) m
    have h₃ : ∑ i ∈ Finset.range m, c (k + 1 + i) =
        ∑ i ∈ Finset.range m, c (k + ((i + 1 : ℕ) : ℤ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      ring
    rw [h₃]
    have h₄ : c (k + ((0 : ℕ) : ℤ)) = c (k + m) := by
      rw [hc]
      simp
    rw [h₄] at h₂
    exact add_right_cancel (h₂.symm.trans h₁)
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => rw [hstep k, ih]
  | pred k ih =>
    rw [← ih, ← hstep (-(k : ℤ) - 1)]
    congr 1
    funext i
    congr 2
    ring

variable [Group G] [NormedSpace ℝ E] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
  [μ.IsMulLeftInvariant]
  {a : G → ℤ} (ha : ∀ g h, a (g * h) = a g + a h) {m : ℕ} {z : G} (hz : a z = m)
  {Φ : G → E} (hΦ : ∀ g, Φ (z * g) = Φ g)

include ha hz hΦ in
/-- The integral over a level set is unchanged by shifting the level by `m`. -/
theorem integral_levelSet_add (j : ℤ) :
    ∫ g, (levelSet a (j + m)).indicator Φ g ∂μ = ∫ g, (levelSet a j).indicator Φ g ∂μ := by
  have h : ∀ g, (levelSet a (j + m)).indicator Φ (z * g) = (levelSet a j).indicator Φ g := by
    intro g
    by_cases hg : a g = j
    · rw [Set.indicator_of_mem (show g ∈ levelSet a j from hg), Set.indicator_of_mem, hΦ]
      change a (z * g) = j + m
      rw [ha, hz, hg]
      ring
    · rw [Set.indicator_of_notMem (show g ∉ levelSet a j from hg), Set.indicator_of_notMem]
      change ¬ a (z * g) = j + m
      rw [ha, hz]
      omega
  calc ∫ g, (levelSet a (j + m)).indicator Φ g ∂μ
      = ∫ g, (levelSet a (j + m)).indicator Φ (z * g) ∂μ :=
        (integral_mul_left_eq_self _ z).symm
    _ = ∫ g, (levelSet a j).indicator Φ g ∂μ := by simp_rw [h]

omit [Group G] [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- The window integral is the sum of the level-set integrals. -/
theorem integral_window_eq_sum (hint : ∀ j, Integrable ((levelSet a j).indicator Φ) μ)
    (k : ℤ) :
    ∫ g, (window a m k).indicator Φ g ∂μ =
      ∑ i ∈ Finset.range m, ∫ g, (levelSet a (k + i)).indicator Φ g ∂μ := by
  simp_rw [window_indicator_eq_sum a m k Φ]
  exact integral_finsetSum _ fun i _ => hint _

include ha hz hΦ in
/-- The window integral does not depend on the position of the window. -/
theorem integral_window_eq_integral_window_zero
    (hint : ∀ j, Integrable ((levelSet a j).indicator Φ) μ) (k : ℤ) :
    ∫ g, (window a m k).indicator Φ g ∂μ = ∫ g, (window a m 0).indicator Φ g ∂μ := by
  rw [integral_window_eq_sum μ hint, integral_window_eq_sum μ hint]
  have := sum_range_shift_of_periodic (m := m)
    (fun j => ∫ g, (levelSet a j).indicator Φ g ∂μ)
    (integral_levelSet_add μ ha hz hΦ) k
  simpa using this

include ha hz hΦ in
/-- **Left invariance of the window integral.** For a `z`-periodic function `Φ`, integrable on
every level set, the window integral of every left translate `g ↦ Φ (h * g)` equals that of
`Φ`. -/
theorem integral_window_comp_mul_left
    (hint : ∀ j, Integrable ((levelSet a j).indicator Φ) μ) (h : G) :
    ∫ g, (window a m 0).indicator (fun g => Φ (h * g)) g ∂μ =
      ∫ g, (window a m 0).indicator Φ g ∂μ := by
  have hpt : ∀ g, (window a m 0).indicator (fun g => Φ (h * g)) g =
      (window a m (a h)).indicator Φ (h * g) := by
    intro g
    by_cases hg : g ∈ window a m 0
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
      obtain ⟨h₁, h₂⟩ := hg
      change a h ≤ a (h * g) ∧ a (h * g) < a h + m
      rw [ha]
      constructor <;> omega
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
      intro hhg
      apply hg
      obtain ⟨h₁, h₂⟩ := hhg
      rw [ha] at h₁ h₂
      exact ⟨by omega, by omega⟩
  simp_rw [hpt]
  rw [integral_mul_left_eq_self (fun g => (window a m (a h)).indicator Φ g) h]
  exact integral_window_eq_integral_window_zero μ ha hz hΦ hint (a h)

end Langlands.BaseChange.PeriodicWindow
