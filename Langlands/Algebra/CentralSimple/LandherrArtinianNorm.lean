import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination

/-! # Binary norm equations in commutative Artinian rings -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

/-- If `2` is a unit, `1 + n` is a square for every nilpotent `n`. -/
theorem exists_sq_eq_one_add_of_isNilpotent {R : Type*} [CommRing R] (h2 : IsUnit (2 : R))
    {n : R} (hn : IsNilpotent n) : ∃ w : R, w ^ 2 = 1 + n := by
  obtain ⟨k, hk⟩ := hn
  have hk' : n ^ (2 ^ k) = 0 := pow_eq_zero_of_le (Nat.lt_two_pow_self).le hk
  clear hk
  induction k generalizing n with
  | zero => exact ⟨1, by rw [pow_zero, pow_one] at hk'; rw [hk']; ring⟩
  | succ k ih =>
    obtain ⟨h, hh⟩ := h2.exists_left_inv
    set w₀ := 1 + h * n with hw₀
    have hnil : IsNilpotent (h * n) := ⟨2 ^ (k + 1), by rw [mul_pow, hk', mul_zero]⟩
    have hw₀u : IsUnit w₀ := hnil.isUnit_one_add
    obtain ⟨g, hg⟩ := hw₀u.exists_left_inv
    set m := -(h * n) ^ 2 * g ^ 2 with hm
    have hm' : m ^ (2 ^ k) = 0 := by
      have : m = n ^ 2 * (-(h ^ 2 * g ^ 2)) := by rw [hm]; ring
      rw [this, mul_pow, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring, hk', zero_mul]
    obtain ⟨w', hw'⟩ := ih (n := m) hm'
    refine ⟨w₀ * w', ?_⟩
    rw [mul_pow, hw', hm, hw₀]
    have h2' : h * 2 = 1 := hh
    have hg' : g * (1 + h * n) = 1 := by rw [← hw₀]; exact hg
    linear_combination n * h2' - (h * n) ^ 2 * (g * (1 + h * n) + 1) * hg'

/-- **Binary norm equations in Artinian rings.** In a commutative Artinian ring in which `2` is a
unit, if `X² - d Y² = c` (with `c` a unit) is solvable modulo every maximal ideal, it is solvable. -/
theorem exists_sq_sub_mul_sq_eq_of_maximal {R : Type*} [CommRing R] [IsArtinianRing R]
    (h2 : IsUnit (2 : R)) (d c : R) (hc : IsUnit c)
    (hloc : ∀ m : Ideal R, m.IsMaximal → ∃ X Y : R, X ^ 2 - d * Y ^ 2 - c ∈ m) :
    ∃ X Y : R, X ^ 2 - d * Y ^ 2 = c := by
  classical
  let ι := {m : Ideal R // m.IsMaximal}
  have : Finite ι := (IsArtinianRing.setOfPred_isMaximal_finite R).to_subtype
  choose X Y hXY using fun i : ι => hloc i.1 i.2
  have hcop : Pairwise (Function.onFun IsCoprime fun i : ι => i.1) := by
    intro i j hij
    have := i.2
    have := j.2
    exact Ideal.isCoprime_of_isMaximal (fun h => hij (Subtype.ext h))
  let e := Ideal.quotientInfRingEquivPiQuotient (fun i : ι => i.1) hcop
  obtain ⟨X₀', hX₀'⟩ := e.surjective (fun i => Ideal.Quotient.mk i.1 (X i))
  obtain ⟨Y₀', hY₀'⟩ := e.surjective (fun i => Ideal.Quotient.mk i.1 (Y i))
  obtain ⟨X₀, rfl⟩ := Ideal.Quotient.mk_surjective X₀'
  obtain ⟨Y₀, rfl⟩ := Ideal.Quotient.mk_surjective Y₀'
  have hmem : ∀ i : ι, X₀ ^ 2 - d * Y₀ ^ 2 - c ∈ i.1 := by
    intro i
    have hx : Ideal.Quotient.mk i.1 X₀ = Ideal.Quotient.mk i.1 (X i) := congrFun hX₀' i
    have hy : Ideal.Quotient.mk i.1 Y₀ = Ideal.Quotient.mk i.1 (Y i) := congrFun hY₀' i
    have h := hXY i
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
    simp only [map_sub, map_mul, map_pow] at h ⊢
    rw [hx, hy]
    exact h
  have hnil : IsNilpotent (X₀ ^ 2 - d * Y₀ ^ 2 - c) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    exact hmem ⟨J, (IsArtinianRing.isPrime_iff_isMaximal J).mp hJ⟩
  set u := hc.unit with hu
  set n := ((u⁻¹ : Rˣ) : R) * (X₀ ^ 2 - d * Y₀ ^ 2 - c) with hn
  have hn' : IsNilpotent n := (Commute.all _ _).isNilpotent_mul_left hnil
  obtain ⟨w, hw⟩ := exists_sq_eq_one_add_of_isNilpotent h2 hn'
  have hwu : IsUnit w := by
    have : IsUnit (w ^ 2) := by rw [hw]; exact hn'.isUnit_one_add
    exact (isUnit_pow_iff (by norm_num)).mp this
  set v := hwu.unit with hv
  refine ⟨X₀ * ((v⁻¹ : Rˣ) : R), Y₀ * ((v⁻¹ : Rˣ) : R), ?_⟩
  have hvw : (v : R) = w := rfl
  have h1 : (X₀ ^ 2 - d * Y₀ ^ 2) = c * (1 + n) := by
    rw [hn, mul_add, mul_one, ← mul_assoc, show c = (u : R) from rfl, Units.mul_inv, one_mul]
    ring
  have h3 : ((v⁻¹ : Rˣ) : R) ^ 2 * (1 + n) = 1 := by
    rw [← hw, ← hvw, ← mul_pow, Units.inv_mul, one_pow]
  calc (X₀ * ((v⁻¹ : Rˣ) : R)) ^ 2 - d * (Y₀ * ((v⁻¹ : Rˣ) : R)) ^ 2
      = (X₀ ^ 2 - d * Y₀ ^ 2) * ((v⁻¹ : Rˣ) : R) ^ 2 := by ring
    _ = c * (((v⁻¹ : Rˣ) : R) ^ 2 * (1 + n)) := by rw [h1]; ring
    _ = c := by rw [h3, mul_one]

end Langlands.CentralSimple.Landherr
