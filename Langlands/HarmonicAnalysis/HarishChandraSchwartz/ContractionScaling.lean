import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-! # An inverse power bound from a contraction-scaling argument

Abstract topological lemma for the proof of Waldspurger 2003, II.2: a size function `β`
that is expanded by at most the factor `q ^ D` under a map `c`, and a function `g` that
`c` shrinks by at least the factor `q`, satisfy `β ≤ C g ^ D` wherever `1 ≤ β`, provided
`g` is continuous and positive on the compact annulus `{1 ≤ q ^ D β, β ≤ 1}` and every
point is eventually moved into `{β ≤ 1}`. No group structure is used.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

section ContractionScaling

variable {X : Type*}

/-- The annulus `{x | 1 ≤ q ^ D β x ∧ β x ≤ 1}` of the contraction-scaling argument. -/
def contractionScalingAnnulus (β : X → ℝ) (q : ℝ) (D : ℕ) : Set X :=
  {x | 1 ≤ q ^ D * β x ∧ β x ≤ 1}

theorem le_pow_mul_iterate_of_le_mul {c : X → X} {β : X → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hβ : ∀ x, β x ≤ K * β (c x)) (n : ℕ) (x : X) : β x ≤ K ^ n * β (c^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ', mul_assoc]
    exact (hβ x).trans (mul_le_mul_of_nonneg_left (ih (c x)) hK)

theorem pow_mul_iterate_le_of_mul_le {c : X → X} {g : X → ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hg : ∀ x, q * g (c x) ≤ g x) (n : ℕ) (x : X) : q ^ n * g (c^[n] x) ≤ g x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ', mul_assoc]
    exact (mul_le_mul_of_nonneg_left (ih (c x)) hq).trans (hg x)

/-- If `β (c x) ≤ θ β x` with `0 ≤ θ < 1`, every point is eventually moved into
`{β ≤ 1}`. -/
theorem exists_iterate_le_one_of_le_mul {c : X → X} {β : X → ℝ} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hβ : ∀ x, β (c x) ≤ θ * β x) (x : X) : ∃ n, β (c^[n] x) ≤ 1 := by
  have hle : ∀ n, β (c^[n] x) ≤ θ ^ n * β x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
      exact (hβ _).trans (mul_le_mul_of_nonneg_left ih hθ0)
  have ht : Filter.Tendsto (fun n : ℕ => θ ^ n * β x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const (β x)
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds zero_lt_one)).exists
  exact ⟨n, (hle n).trans hn⟩

/-- The contraction-scaling inverse bound. Let `q ≥ 1`, `D : ℕ`, `c : X → X`,
`β g : X → ℝ` with `β x ≤ q ^ D β (c x)`, `q g (c x) ≤ g x`, every point eventually moved
into `{β ≤ 1}`, the annulus compact and `g` continuous and positive on it. Then
`β x ≤ C g x ^ D` for some `C > 0` and all `x` with `1 ≤ β x`. -/
theorem exists_le_mul_pow_of_contractionScaling [TopologicalSpace X] {c : X → X} {β g : X → ℝ} {q : ℝ} {D : ℕ}
    (hq1 : 1 ≤ q) (hβ : ∀ x, β x ≤ q ^ D * β (c x)) (hg : ∀ x, q * g (c x) ≤ g x)
    (hreach : ∀ x, ∃ n, β (c^[n] x) ≤ 1)
    (hS : IsCompact (contractionScalingAnnulus β q D))
    (hgc : ContinuousOn g (contractionScalingAnnulus β q D))
    (hgpos : ∀ x ∈ contractionScalingAnnulus β q D, 0 < g x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 1 ≤ β x → β x ≤ C * g x ^ D := by
  set S := contractionScalingAnnulus β q D
  have hq : 0 ≤ q := zero_le_one.trans hq1
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y ∈ S, m ≤ g y := by
    rcases S.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, by simp [hE]⟩
    · obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hgc
      exact ⟨g y₀, hgpos y₀ hy₀, fun y hy => hmin hy⟩
  have hqD : 0 ≤ q ^ D := pow_nonneg hq D
  refine ⟨(m ^ D)⁻¹, inv_pos.2 (pow_pos hm0 D), fun x hx => ?_⟩
  classical
  let n := Nat.find (hreach x)
  have hn : β (c^[n] x) ≤ 1 := Nat.find_spec (hreach x)
  have hmem : c^[n] x ∈ S := by
    refine ⟨?_, hn⟩
    rcases hn0 : n with _ | k
    · simp only [Function.iterate_zero, id]
      exact hx.trans (le_mul_of_one_le_left (by linarith) (one_le_pow₀ hq1))
    · have hk : ¬ β (c^[k] x) ≤ 1 := Nat.find_min (hreach x) (by omega)
      have h1 := hβ (c^[k] x)
      rw [← Function.iterate_succ_apply' c k x] at h1
      linarith [not_le.1 hk]
  have hβx : β x ≤ (q ^ n) ^ D := by
    calc β x ≤ (q ^ D) ^ n * β (c^[n] x) := le_pow_mul_iterate_of_le_mul hqD hβ n x
      _ ≤ (q ^ D) ^ n * 1 := mul_le_mul_of_nonneg_left hn (pow_nonneg hqD n)
      _ = (q ^ n) ^ D := by rw [mul_one, ← pow_mul, ← pow_mul, mul_comm]
  have hgx : q ^ n * m ≤ g x :=
    (mul_le_mul_of_nonneg_left (hm _ hmem) (pow_nonneg hq n)).trans
      (pow_mul_iterate_le_of_mul_le hq hg n x)
  have hpow : (q ^ n * m) ^ D ≤ g x ^ D :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hq n) hm0.le) hgx D
  have hmD : 0 < m ^ D := pow_pos hm0 D
  calc β x ≤ (q ^ n) ^ D := hβx
    _ = (m ^ D)⁻¹ * (q ^ n * m) ^ D := by
      rw [mul_pow]; field_simp
    _ ≤ (m ^ D)⁻¹ * g x ^ D := mul_le_mul_of_nonneg_left hpow (inv_nonneg.2 hmD.le)

end ContractionScaling

end Langlands.HarishChandraSchwartz
