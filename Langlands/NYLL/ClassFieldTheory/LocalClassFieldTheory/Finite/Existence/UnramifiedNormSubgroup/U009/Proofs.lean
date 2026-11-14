/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 531, 2026-11-14: adapt M266.009 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and prove the published closed Statement target.
Replace the source imports by the focused published target module and
reduce directly to Mathlib's integer-cast divisibility criterion.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.MultiplicativeStatements

/-!
# Trivial multiplicative reduced valuation and divisibility

Source: M266.009, lines 96–103 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- A unit maps to one exactly when its valuation is divisible by the degree. -/
theorem valuationModDegreeMulHom_eq_one_iff_dvd :
    valuationModDegreeMulHom_eq_one_iff_dvdStatement.{u} := by
  intro K _ _ _ _ n x
  change (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
    (Additive.ofMul x) : ZMod n) = 0 ↔ _
  exact ZMod.intCast_zmod_eq_zero_iff_dvd
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)) n

end Langlands.NYLL.LocalClassFieldTheory
