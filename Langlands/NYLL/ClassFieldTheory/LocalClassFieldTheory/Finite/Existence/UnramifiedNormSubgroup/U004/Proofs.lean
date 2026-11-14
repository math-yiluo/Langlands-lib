/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 527, 2026-11-14: extract the M266.004 proof from
commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the exact published closed proposition target,
import its statement module, and replace the source evaluation rewrite
with definitional evaluation of the published reduced valuation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.AdditiveStatements

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The reduced valuation vanishes exactly when the degree divides the normalized valuation. -/
theorem valuationModDegree_eq_zero_iff_dvd.{u} :
    valuationModDegree_eq_zero_iff_dvdStatement.{u} := by
  intro K _ _ _ _ n x
  change (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x : ZMod n) = 0 ↔
    (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x
  exact ZMod.intCast_zmod_eq_zero_iff_dvd
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K x) n

end Langlands.NYLL.LocalClassFieldTheory
