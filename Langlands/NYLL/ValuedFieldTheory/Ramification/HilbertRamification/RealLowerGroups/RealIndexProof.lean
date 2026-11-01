/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1045, 2026-11-01, with source extraction, grouping and
parameter analysis contributed by Worker 106: extract the theorems and proofs
of M304.005–.008 and M304.010–.013 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, reuse the published exponent and ideal definitions, omit unused
section parameters, replace the docstrings, prove three ideal clauses by
rewriting with the exponent theorems instead of simp, and add the closed
theorem realRamificationIndexProperties conjoining the eight theorems.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndexStatement
import Mathlib.Tactic.Linarith

/-!
# Real-index exponent and ideal properties: proof

This module proves the closed proposition `RealRamificationIndexPropertiesStatement`.
The eight theorems are M304.005–.008 (lines 111–135) and M304.010–.013
(lines 142–162) of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`.
-/

universe w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

variable {L : Type w} [Field L]
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}

/-- The real-index exponent is monotone. -/
theorem realRamificationExponent_mono :
    Monotone realRamificationExponent := by
  intro s t hst
  apply Int.toNat_le_toNat
  apply Int.ceil_mono
  linarith

/-- The real-index exponent vanishes at `-1`. -/
@[simp] theorem realRamificationExponent_neg_one :
    realRamificationExponent (-1) = 0 := by
  simp [realRamificationExponent]

/-- The real-index exponent vanishes at every index `s ≤ -1`. -/
theorem realRamificationExponent_eq_zero_of_le_neg_one
    {s : ℝ} (hs : s ≤ -1) :
    realRamificationExponent s = 0 := by
  rw [realRamificationExponent, Int.toNat_eq_zero]
  have hs' : s + 1 ≤ 0 := by linarith
  exact Int.ceil_le.mpr (by simpa using hs')

/-- At a natural index `n` the real-index exponent is `n + 1`. -/
@[simp] theorem realRamificationExponent_nat (n : ℕ) :
    realRamificationExponent (n : ℝ) = n + 1 := by
  simp [realRamificationExponent]

/-- The real-index ideals decrease as the index increases. -/
theorem realRamificationIdeal_antitone {s t : ℝ} (hst : s ≤ t) :
    realRamificationIdeal target t ≤ realRamificationIdeal target s :=
  Ideal.pow_le_pow_right (realRamificationExponent_mono hst)

/-- The real-index ideal at `-1` is the whole valuation ring. -/
@[simp] theorem realRamificationIdeal_neg_one :
    realRamificationIdeal target (-1) = ⊤ := by
  rw [realRamificationIdeal, realRamificationExponent_neg_one, pow_zero, Ideal.one_eq_top]

/-- At a natural index `n` the real-index ideal is the `(n + 1)`-st power of the
maximal ideal. -/
@[simp] theorem realRamificationIdeal_nat (n : ℕ) :
    realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1) := by
  rw [realRamificationIdeal, realRamificationExponent_nat]

/-- The real-index ideal is the whole valuation ring at every index `s ≤ -1`. -/
theorem realRamificationIdeal_eq_top_of_le_neg_one
    {s : ℝ} (hs : s ≤ -1) :
    realRamificationIdeal target s = ⊤ := by
  rw [realRamificationIdeal, realRamificationExponent_eq_zero_of_le_neg_one hs, pow_zero,
    Ideal.one_eq_top]

/-- The eight real-index exponent and ideal properties, for every field and
chosen DVF. -/
theorem realRamificationIndexProperties :
    RealRamificationIndexPropertiesStatement.{w, x} :=
  ⟨realRamificationExponent_mono, realRamificationExponent_neg_one,
    realRamificationExponent_eq_zero_of_le_neg_one, realRamificationExponent_nat,
    fun _ => ⟨realRamificationIdeal_antitone, realRamificationIdeal_neg_one,
      realRamificationIdeal_nat, realRamificationIdeal_eq_top_of_le_neg_one⟩⟩

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
