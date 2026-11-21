import Langlands.BushnellKutzko.CriticalDerivedSymbols

/-! # Commutation one step beyond a filtration degree -/

noncomputable section

namespace Langlands.BushnellKutzko.CriticalDerived

variable {O F V : Type*} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module O V] [Module F V] [IsScalarTower O F V]
  (C : LatticeChain O F V) (x : Module.End F V)

/-- Endomorphisms whose commutator with `x` is at least one step beyond degree `j`.
Membership here tests only the commutator, not the depth of the endomorphism. -/
def leadingCommutant (j : ℤ) : Submodule O (Module.End F V) :=
  (C.endFiltration (j + 1)).comap (-adjointMap O x)

variable {C x} {j k : ℤ} {y z : Module.End F V}

@[simp] theorem mem_leadingCommutant : y ∈ leadingCommutant C x j ↔
    y * x - x * y ∈ C.endFiltration (j + 1) := by
  change -(x * y - y * x) ∈ C.endFiltration (j + 1) ↔ _
  rw [neg_sub]

namespace LeadingCommutant

theorem of_commute (j : ℤ) (h : Commute y x) : y ∈ leadingCommutant C x j := by
  rw [mem_leadingCommutant, h.eq, sub_self]
  exact zero_mem _

theorem antitone : Antitone (leadingCommutant C x) := by
  intro a b hab f hf
  exact mem_leadingCommutant.mpr (C.endFiltration_antitone (by omega) (mem_leadingCommutant.mp hf))

theorem mul_mem (hy : y ∈ C.endFiltration j) (hz : z ∈ C.endFiltration k)
    (hyc : y ∈ leadingCommutant C x j) (hzc : z ∈ leadingCommutant C x k) :
    y * z ∈ leadingCommutant C x (j + k) := by
  rw [mem_leadingCommutant] at hyc hzc ⊢
  rw [show y * z * x - x * (y * z) = y * (z * x - x * z) + (y * x - x * y) * z by noncomm_ring]
  exact add_mem (by simpa only [add_assoc] using C.mul_mem_endFiltration hy hzc)
    (by rw [show j + k + 1 = j + 1 + k by omega]; exact C.mul_mem_endFiltration hyc hz)

variable {g : (Module.End F V)ˣ}

theorem inv_mem (hg : Shifts C j g) (hgc : (g : Module.End F V) ∈ leadingCommutant C x j) :
    (↑(g⁻¹) : Module.End F V) ∈ leadingCommutant C x (-j) := by
  rw [mem_leadingCommutant] at hgc ⊢
  have heq : (↑(g⁻¹) : Module.End F V) * x - x * ↑(g⁻¹) =
      (↑(g⁻¹) : Module.End F V) * -((g : Module.End F V) * x - x * g) * ↑(g⁻¹) := by
    simp only [neg_sub, mul_sub, sub_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [mul_assoc _ (g : Module.End F V), ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [heq, show -j + 1 = -j + (j + 1) + -j by omega]
  exact C.mul_mem_endFiltration (C.mul_mem_endFiltration hg.2 (neg_mem hgc)) hg.2

theorem pow_mem (hg : Shifts C j g) (hgc : (g : Module.End F V) ∈ leadingCommutant C x j)
    (n : ℕ) : (↑(g ^ n) : Module.End F V) ∈ leadingCommutant C x ((n : ℤ) * j) := by
  induction n with
  | zero => simpa only [pow_zero, Units.val_one, Nat.cast_zero, zero_mul] using
      (of_commute (C := C) 0 (Commute.one_left x))
  | succ n ih => simpa only [pow_succ, Units.val_mul, Nat.cast_succ, add_mul, one_mul] using
      (mul_mem (hg.pow n).1 hg.1 ih hgc)

theorem zpow_mem (hg : Shifts C j g) (hgc : (g : Module.End F V) ∈ leadingCommutant C x j)
    (n : ℤ) : (↑(g ^ n) : Module.End F V) ∈ leadingCommutant C x (n * j) := by
  cases n with
  | ofNat n => exact pow_mem hg hgc n
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by simp [Int.negSucc_eq], neg_mul, zpow_neg, zpow_natCast]
    exact inv_mem (hg.pow _) (pow_mem hg hgc _)

end LeadingCommutant

end Langlands.BushnellKutzko.CriticalDerived
