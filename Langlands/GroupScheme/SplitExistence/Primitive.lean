import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.ZMod.Basic

/-!
# Primitive integral matrices

An integral matrix `B` is *primitive* when it is nonzero modulo every prime `p`, that is, the
gcd of its entries is `1`. If an integral matrix `A` is a rational multiple `q • B` of a
primitive matrix `B`, then `q` is an integer; if `A` is primitive as well, then `q = ± 1`.
Conjugation by an integral matrix with an integral left inverse preserves primitivity.
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {ι : Type*}

/-- An integral matrix is zero modulo `p` exactly when `p` divides all its entries. -/
theorem map_zmod_eq_zero_iff (B : Matrix ι ι ℤ) (p : ℕ) :
    B.map (Int.castRingHom (ZMod p)) = 0 ↔ ∀ c d, (p : ℤ) ∣ B c d := by
  constructor
  · intro h c d
    have := congrFun (congrFun h c) d
    rw [map_apply, zero_apply, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact this
  · intro h
    ext c d
    rw [map_apply, zero_apply, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h c d

/-- If an integral matrix `A` is a rational multiple `q • B` of an integral matrix `B` that is
nonzero modulo every prime, then `q` is an integer `z` and `A = z • B`. -/
theorem exists_int_of_map_eq_smul {A B : Matrix ι ι ℤ} {q : ℚ}
    (hB : ∀ p : ℕ, p.Prime → B.map (Int.castRingHom (ZMod p)) ≠ 0)
    (h : A.map (Int.castRingHom ℚ) = q • B.map (Int.castRingHom ℚ)) :
    ∃ z : ℤ, q = z ∧ A = z • B := by
  have hentry : ∀ c d, (A c d : ℚ) = q * B c d := fun c d => by
    have := congrFun (congrFun h c) d
    simpa using this
  have hden : q.den = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    apply hB p hp
    rw [map_zmod_eq_zero_iff]
    intro c d
    have hint : (q.den : ℤ) * A c d = q.num * B c d := by
      have h1 : ((q.den : ℤ) * A c d : ℚ) = (q.num * B c d : ℤ) := by
        push_cast
        rw [hentry, ← mul_assoc, Rat.den_mul_eq_num]
      exact_mod_cast h1
    have hpdvd : (p : ℤ) ∣ q.num * B c d := by
      rw [← hint]
      exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hpd) _
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpdvd with hnum | hBcd
    · exfalso
      have hpn : p ∣ q.num.natAbs := Int.natCast_dvd.mp hnum
      have hcop := q.reduced
      have : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpn hpd
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · exact hBcd
  refine ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm, ?_⟩
  ext c d
  have h1 : (A c d : ℚ) = ((q.num * B c d : ℤ) : ℚ) := by
    push_cast
    rw [hentry, Rat.coe_int_num_of_den_eq_one hden]
  rw [smul_apply, smul_eq_mul]
  exact_mod_cast h1

/-- If two integral matrices that are nonzero modulo every prime are rational multiples of
each other, `A = q • B`, then `q = ± 1`. -/
theorem eq_one_or_eq_neg_one_of_map_eq_smul {A B : Matrix ι ι ℤ} {q : ℚ}
    (hA : ∀ p : ℕ, p.Prime → A.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hB : ∀ p : ℕ, p.Prime → B.map (Int.castRingHom (ZMod p)) ≠ 0)
    (h : A.map (Int.castRingHom ℚ) = q • B.map (Int.castRingHom ℚ)) :
    ∃ z : ℤ, (z = 1 ∨ z = -1) ∧ q = z ∧ A = z • B := by
  obtain ⟨z, hq, hAB⟩ := exists_int_of_map_eq_smul hB h
  refine ⟨z, ?_, hq, hAB⟩
  have habs : z.natAbs = 1 := by
    by_contra hz
    obtain ⟨p, hp, hpz⟩ := Nat.exists_prime_and_dvd hz
    apply hA p hp
    rw [map_zmod_eq_zero_iff]
    intro c d
    rw [hAB, smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (Int.natCast_dvd.mpr hpz) _
  rcases Int.natAbs_eq_iff.mp habs with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

/-- An integral matrix that is nonzero modulo some prime is nonzero over `ℚ`. -/
theorem map_rat_ne_zero {B : Matrix ι ι ℤ} {p : ℕ} (hB : B.map (Int.castRingHom (ZMod p)) ≠ 0) :
    B.map (Int.castRingHom ℚ) ≠ 0 := by
  intro h
  apply hB
  ext c d
  have := congrFun (congrFun h c) d
  simp only [map_apply, zero_apply, eq_intCast, Int.cast_eq_zero] at this
  simp [this]

/-- Conjugation by a matrix with a left inverse preserves being nonzero after a ring
homomorphism. -/
theorem map_conj_ne_zero [Fintype ι] [DecidableEq ι] {S : Type*} [Ring S] (f : ℤ →+* S)
    {g g' A : Matrix ι ι ℤ} (hg : g' * g = 1) (hA : A.map f ≠ 0) :
    (g * A * g').map f ≠ 0 := by
  intro h
  apply hA
  have : A = g' * (g * A * g') * g := by
    rw [show g' * (g * A * g') * g = (g' * g) * A * (g' * g) by simp only [mul_assoc], hg,
      one_mul, mul_one]
  rw [this, Matrix.map_mul, Matrix.map_mul, h, mul_zero, zero_mul]

end Langlands.GroupScheme.SplitExistence
