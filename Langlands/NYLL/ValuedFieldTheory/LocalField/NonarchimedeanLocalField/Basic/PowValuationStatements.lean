/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 85, 13 November 2026: extract the types of the source
theorems `v_pow` and `v_zpow` (units M128.008 and M128.009) from upstream
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition. Proofs are omitted; the import is reduced to the dependency of the
statements. See the paired Markdown for details. The original LICENSE and
NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Statement target for source unit M128.008: raising a field unit to a natural power
multiplies its normalized valuation by that power. -/
def v_powStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat),
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)

/-- Statement target for source unit M128.009: raising a field unit to an integral power
multiplies its normalized valuation by that integer. -/
def v_zpowStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int),
    v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x)

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
