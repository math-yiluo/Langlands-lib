/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Workers 60 and 106, 2026-11-01: extract only M304.004 and M304.009
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, reuse the published DVF bundle,
omit unused section parameters and replace the full source imports by the
data definitions' dependencies. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Real indices for the chosen maximal-ideal filtration

This module extracts the exponent and ideal definitions from lines 103–109
and 137–140 of NYLL `RealLowerGroups.lean`.
-/

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

noncomputable section

universe w x

/-- The natural exponent for a real lower ramification index, truncated at zero. -/
def realRamificationExponent (s : ℝ) : ℕ :=
  (Int.ceil (s + 1)).toNat

/-- The power of the chosen valuation ring's maximal ideal at real index `s`. -/
def realRamificationIdeal {L : Type w} [Field L]
    (target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ) : Ideal target.valuationSubring :=
  target.maximalIdeal ^ realRamificationExponent s

end

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
