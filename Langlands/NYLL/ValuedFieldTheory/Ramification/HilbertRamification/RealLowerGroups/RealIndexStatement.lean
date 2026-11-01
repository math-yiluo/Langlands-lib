/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1045, 2026-11-01, with source extraction, grouping and
parameter analysis contributed by Worker 106: extract the signatures of
M304.005–.008 and M304.010–.013 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 and conjoin them as one closed Prop
target; prefix the namespace with Langlands.NYLL, reuse the published exponent
and ideal definitions, quantify the field and chosen DVF inside the ideal
clauses, and omit unused section parameters. The proofs are omitted.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndex

/-!
# Real-index exponent and ideal properties: statement

This closed proposition conjoins the signatures of M304.005–.008 (lines 111–135)
and M304.010–.013 (lines 142–162) of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`.
-/

universe w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- The real-index exponent is monotone, vanishes at and below `-1` and equals
`n + 1` at a natural index `n`; for every chosen DVF the corresponding powers of
its maximal ideal decrease with the index, are the whole valuation ring at and
below `-1` and equal the `(n + 1)`-st maximal-ideal power at a natural index `n`. -/
def RealRamificationIndexPropertiesStatement : Prop :=
  Monotone realRamificationExponent ∧
  realRamificationExponent (-1) = 0 ∧
  (∀ {s : ℝ}, s ≤ -1 → realRamificationExponent s = 0) ∧
  (∀ n : ℕ, realRamificationExponent (n : ℝ) = n + 1) ∧
  (∀ {L : Type w} [Field L]
      (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L),
    (∀ {s t : ℝ}, s ≤ t → realRamificationIdeal target t ≤ realRamificationIdeal target s) ∧
    realRamificationIdeal target (-1) = ⊤ ∧
    (∀ n : ℕ, realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1)) ∧
    (∀ {s : ℝ}, s ≤ -1 → realRamificationIdeal target s = ⊤))

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
