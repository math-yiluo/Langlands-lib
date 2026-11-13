/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 201 on 2026-11-13: extracted M133.058 at source commit
fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued definition,
preserving the source universe, ordered telescope and proposition. Added
Langlands.NYLL and omitted the theorem proof. Reused the published successor
quotient by Lean name. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The exact proposition of source unit M133.058; no proof is supplied here. -/
def finite_principalUnitsSuccQuotStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (hn : 1 ≤ n) : Prop :=
    Finite (PrincipalUnitsSuccQuot K n)

end Langlands.NYLL.LocalFieldTheory
