/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Data.PNat.Defs

/-!
# Positive integers ordered by divisibility

`PNat.DvdOrder` is a type synonym of `ℕ+` whose partial order is divisibility. It indexes
diagrams such as the torsion filtration `n ↦ F[n]` of an abelian sheaf.
-/

@[expose] public section

/-- The positive integers `ℕ+` with the divisibility order: `n ≤ m` if and only if `n ∣ m`. -/
def PNat.DvdOrder : Type := ℕ+

namespace PNat.DvdOrder

/-- The positive integer underlying an element of `DvdOrder`. -/
def toPNat (n : DvdOrder) : ℕ+ := n

/-- The underlying natural number. -/
def val (n : DvdOrder) : ℕ := PNat.val n.toPNat

theorem val_pos (n : DvdOrder) : 0 < n.val := PNat.pos n.toPNat

instance : PartialOrder DvdOrder where
  le n m := n.val ∣ m.val
  lt n m := n.val ∣ m.val ∧ ¬m.val ∣ n.val
  le_refl n := Nat.dvd_refl n.val
  le_trans _ _ _ hnm hmk := Nat.dvd_trans hnm hmk
  le_antisymm n m hnm hmn := PNat.eq (m := n.toPNat) (n := m.toPNat) (Nat.dvd_antisymm hnm hmn)
  lt_iff_le_not_ge := by intro a b; rfl

theorem le_iff_dvd {n m : DvdOrder} : n ≤ m ↔ n.val ∣ m.val := Iff.rfl


end PNat.DvdOrder
