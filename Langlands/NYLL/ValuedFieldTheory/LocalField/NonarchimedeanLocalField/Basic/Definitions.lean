/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 384 on 2026-10-25: extracted only source unit M128.001
from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709 and added the
Langlands.NYLL namespace prefix. The definition body and its sign are unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic

/-!
# Normalized integer valuation of a nonarchimedean local field

This module contains only the source normalized integer valuation on field units.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The normalized integer valuation attached to a nonarchimedean local field.

It is obtained by transporting the value group to `WithZero (Multiplicative Int)` and then taking
the exponent of the nonzero value of a field unit. -/
noncomputable def v (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ → Int :=
  fun x =>
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Additive.toMul x).ne_zero)))

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
