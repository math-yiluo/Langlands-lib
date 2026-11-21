import Langlands.BushnellKutzko.CriticalDerivedCyclicLift
import Mathlib.Data.Int.GCD

/-! # Bézout change of the two commuting generators -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.CriticalDerived

/-- Write the period and the signed depth with common positive divisor `g`, and record a
Bézout identity for the two quotients. -/
structure ShiftParameters (e : ℕ) (d : ℤ) where
  g : ℕ
  h : ℕ
  k : ℤ
  u : ℤ
  v : ℤ
  g_pos : 0 < g
  h_pos : 0 < h
  period_eq : e = h * g
  depth_eq : d = (g : ℤ) * k
  bezout : u * k + v * (h : ℤ) = 1

theorem exists_shiftParameters {e : ℕ} (he : 0 < e) (d : ℤ) : Nonempty (ShiftParameters e d) := by
  let g := d.gcd (e : ℤ)
  have hdiv : (g : ℤ) ∣ (e : ℤ) := Int.gcd_dvd_right ..
  have hg : 0 < g := by
    by_contra! h
    have h0 : g = 0 := by omega
    simp only [h0, Nat.cast_zero, zero_dvd_iff, Nat.cast_eq_zero] at hdiv
    omega
  obtain ⟨h, hge⟩ := Int.natCast_dvd_natCast.mp hdiv
  obtain ⟨k, hk⟩ : (g : ℤ) ∣ d := Int.gcd_dvd_left ..
  have hh : 0 < h := by
    by_contra! ht
    have h0 : h = 0 := by omega
    simp [h0, he.ne'] at hge
  let u := Int.gcdA d (e : ℤ)
  let v := Int.gcdB d (e : ℤ)
  refine ⟨⟨g, h, k, u, v, hg, hh, hge.trans (Nat.mul_comm ..), hk, ?_⟩⟩
  have hge' : (e : ℤ) = (g : ℤ) * (h : ℤ) := by exact_mod_cast hge
  have hab : (g : ℤ) = d * u + (e : ℤ) * v := Int.gcd_eq_gcd_ab d (e : ℤ)
  apply mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast hg.ne')
  calc
    (g : ℤ) * (u * k + v * (h : ℤ)) = d * u + (e : ℤ) * v := by rw [hk, hge']; ring
    _ = (g : ℤ) * 1 := by rw [mul_one, hab]

namespace ShiftParameters

variable {e : ℕ} {d : ℤ} (N : ShiftParameters e d)

theorem residual_degree : (N.h : ℤ) * d + -N.k * (e : ℤ) = 0 := by
  have he : (e : ℤ) = (N.h : ℤ) * (N.g : ℤ) := by exact_mod_cast N.period_eq
  linear_combination (N.h : ℤ) * N.depth_eq - N.k * he

theorem shift_degree : N.u * d + N.v * (e : ℤ) = (N.g : ℤ) := by
  have he : (e : ℤ) = (N.h : ℤ) * (N.g : ℤ) := by exact_mod_cast N.period_eq
  calc
    _ = (N.g : ℤ) * (N.u * N.k + N.v * N.h) := by
      linear_combination N.u * N.depth_eq + N.v * he
    _ = _ := by rw [N.bezout, mul_one]

section Group

variable {G : Type*} [Group G]

/-- The normalized degree-zero generator. -/
def residual (A π : G) : G := A ^ (N.h : ℤ) * π ^ (-N.k)

/-- The generator of the smaller positive shift degree. -/
def shift (A π : G) : G := A ^ N.u * π ^ N.v

theorem residual_commutes_shift {A π : G} (hc : Commute A π) :
    Commute (N.residual A π) (N.shift A π) :=
  (((Commute.refl A).zpow_zpow ..).mul_right (hc.zpow_zpow ..)).mul_left
    (((hc.symm.zpow_zpow ..).mul_right ((Commute.refl π).zpow_zpow ..)))

theorem shift_carry {A π : G} (hc : Commute A π) :
    N.shift A π ^ N.h = π * N.residual A π ^ N.u := by
  rw [shift, residual, ← zpow_natCast, (hc.zpow_zpow ..).mul_zpow, (hc.zpow_zpow ..).mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  have hv : N.v * (N.h : ℤ) = 1 + -N.k * N.u := by nlinarith [N.bezout]
  rw [hv, mul_comm N.u (N.h : ℤ), zpow_add, zpow_one,
    ← mul_assoc, (hc.zpow_left _).eq, mul_assoc]

theorem reconstruct {A π : G} (hc : Commute A π) :
    N.shift A π ^ N.k * N.residual A π ^ N.v = A := by
  rw [shift, residual, (hc.zpow_zpow ..).mul_zpow, (hc.zpow_zpow ..).mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    (hc.symm.zpow_zpow ..).mul_mul_mul_comm, ← zpow_add, ← zpow_add,
    mul_comm (N.h : ℤ) N.v, N.bezout, zpow_one]
  rw [show N.v * N.k + -N.k * N.v = 0 by ring, zpow_zero, mul_one]

theorem carry_reconstruct {S B π : G} (hsb : Commute S B) (hπb : Commute π B)
    (hc : S ^ N.h = π * B ^ N.u) :
    (S ^ N.k * B ^ N.v) ^ N.h = π ^ N.k * B ∧
    (S ^ N.k * B ^ N.v) ^ N.u * π ^ N.v = S := by
  constructor
  · rw [← zpow_natCast, (hsb.zpow_zpow ..).mul_zpow, ← zpow_mul, ← zpow_mul,
      mul_comm N.k (N.h : ℤ), zpow_mul, zpow_natCast, hc, (hπb.zpow_right _).mul_zpow,
      ← zpow_mul, mul_assoc, ← zpow_add, N.bezout, zpow_one]
  · have hB : (B ^ N.v) ^ N.u = (B ^ N.u) ^ N.v := by
      rw [← zpow_mul, ← zpow_mul, mul_comm N.v N.u]
    rw [(hsb.zpow_zpow ..).mul_zpow, ← zpow_mul, mul_assoc,
      hB, ((hπb.zpow_right N.u).zpow_zpow N.v N.v).symm.eq, ← (hπb.zpow_right _).mul_zpow,
      ← hc, ← zpow_natCast, ← zpow_mul, ← zpow_add,
      mul_comm N.k N.u, mul_comm (N.h : ℤ) N.v, N.bezout, zpow_one]

end Group

variable {F V O : Type*} [Field F] [AddCommGroup V] [Module F V] [CommRing O] [Algebra O F]
  [Module O V] [IsScalarTower O F V] {C : LatticeChain O F V}
  {A π : (Module.End F V)ˣ}

/-- The Bézout generators have degrees zero and `g`. -/
theorem shifts_residual_shift (N : ShiftParameters C.period d) (ha : Shifts C d A)
    (hπ : Shifts C C.period π) : Shifts C 0 (N.residual A π) ∧ Shifts C N.g (N.shift A π) := by
  have hr := (ha.zpow (N.h : ℤ)).mul (hπ.zpow (-N.k))
  have hs := (ha.zpow N.u).mul (hπ.zpow N.v)
  exact ⟨N.residual_degree ▸ hr, N.shift_degree ▸ hs⟩

theorem lifted_symbol {z τ z' τ' : (Module.End F V)ˣ}
    (hz : Shifts C 0 z) (ht : Shifts C N.g τ) (hz' : Shifts C 0 z') (ht' : Shifts C N.g τ')
    (hzu : SymbolEq C 0 (z' : Module.End F V) z)
    (htt : SymbolEq C N.g (τ' : Module.End F V) τ) :
    SymbolEq C d (↑(τ' ^ N.k * z' ^ N.v) : Module.End F V) (↑(τ ^ N.k * z ^ N.v)) := by
  have h := (htt.zpow ht' ht N.k).mul (hzu.zpow hz' hz N.v)
  rw [mul_zero, add_zero, mul_comm N.k, ← N.depth_eq] at h
  exact h

end ShiftParameters

end Langlands.BushnellKutzko.CriticalDerived
