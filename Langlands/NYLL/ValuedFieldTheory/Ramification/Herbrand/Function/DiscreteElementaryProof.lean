/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1045, 2026-11-02, with source extraction, grouping and
target design contributed by Worker 106: extract the theorems and proofs of
M303.005–.012 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, reuse the published Herbrand
definitions, omit the local subgroup instances and the noncomputable section,
replace the docstrings, and add the closed theorem herbrandDiscreteElementary
conjoining the eight theorems.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.DiscreteElementaryStatement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Elementary slope and natural-sum laws of the Herbrand function: proof

This module proves the closed proposition `HerbrandDiscreteElementaryStatement`.
The eight theorems are M303.005–.012 (lines 55–109) of
`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

section Laws

variable {G : Type u} [Group G] [Finite G]
variable (F : AntitoneNormalSubgroupFiltration G)

omit [Finite G] in
/-- The natural Herbrand sum vanishes at `0`. -/
@[simp] theorem herbrandValueNat_zero : (herbrandValueNat F) 0 = 0 := by
  simp [herbrandValueNat]

omit [Finite G] in
/-- The natural Herbrand sum at `n + 1` is the sum at `n` plus the slope at `n`. -/
theorem herbrandValueNat_succ (n : ℕ) :
    (herbrandValueNat F) (n + 1) =
      (herbrandValueNat F) n + (herbrandSlope F) n := by
  simp [herbrandValueNat, Finset.sum_range_succ]

/-- For a finite group, every Herbrand slope is positive. -/
theorem herbrandSlope_pos (i : ℕ) :
    0 < (herbrandSlope F) i := by
  have hi : 0 < Nat.card (F.lower (i + 1)) := Finite.card_pos
  have h0 : 0 < Nat.card (F.lower 0) := Finite.card_pos
  exact div_pos (Nat.cast_pos.mpr hi) (Nat.cast_pos.mpr h0)

/-- For a finite group, every Herbrand slope is nonnegative. -/
theorem herbrandSlope_nonneg (i : ℕ) :
    0 ≤ (herbrandSlope F) i :=
  ((herbrandSlope_pos F) i).le

/-- For a finite group, every Herbrand slope is at least `1 / |F.lower 0|`. -/
theorem one_div_card_le_herbrandSlope (i : ℕ) :
    (1 : ℝ) / Nat.card (F.lower 0) ≤ (herbrandSlope F) i := by
  rw [herbrandSlope]
  have h0 : (0 : ℝ) < Nat.card (F.lower 0) := by
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos)
  apply (div_le_div_iff_of_pos_right h0).2
  exact_mod_cast (show 0 < Nat.card (F.lower (i + 1)) from Finite.card_pos)

/-- For a finite group, the natural Herbrand sum is nonnegative. -/
theorem herbrandValueNat_nonneg (n : ℕ) :
    0 ≤ (herbrandValueNat F) n := by
  exact Finset.sum_nonneg fun i _ => (herbrandSlope_nonneg F) i

/-- For a finite group, the natural Herbrand sum at `n` is at least
`n / |F.lower 0|`. -/
theorem nat_div_card_le_herbrandValueNat (n : ℕ) :
    (n : ℝ) / Nat.card (F.lower 0) ≤ (herbrandValueNat F) n := by
  rw [herbrandValueNat]
  calc
    (n : ℝ) / Nat.card (F.lower 0) =
        ∑ _i ∈ Finset.range n, (1 : ℝ) / Nat.card (F.lower 0) := by
          simp [div_eq_mul_inv]
    _ ≤ ∑ i ∈ Finset.range n, (herbrandSlope F) i := by
      exact Finset.sum_le_sum fun i _ => (one_div_card_le_herbrandSlope F) i

/-- For a finite group, the natural Herbrand sum is strictly monotone. -/
theorem herbrandValueNat_strictMono : StrictMono (herbrandValueNat F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [(herbrandValueNat_succ F)]
  exact lt_add_of_pos_right _ ((herbrandSlope_pos F) n)

end Laws

/-- The eight elementary laws M303.005–.012 hold: the first two for every group
and filtration, the other six for every finite group and filtration. -/
theorem herbrandDiscreteElementary : HerbrandDiscreteElementaryStatement.{u} :=
  ⟨fun F => ⟨herbrandValueNat_zero F, herbrandValueNat_succ F⟩,
    fun F => ⟨herbrandSlope_pos F, herbrandSlope_nonneg F,
      one_div_card_le_herbrandSlope F, herbrandValueNat_nonneg F,
      nat_div_card_le_herbrandValueNat F, herbrandValueNat_strictMono F⟩⟩

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
