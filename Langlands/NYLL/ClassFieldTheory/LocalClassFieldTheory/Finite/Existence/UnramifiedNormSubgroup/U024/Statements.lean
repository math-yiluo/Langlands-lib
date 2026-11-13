/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)


Modified by Worker 205, 2026-11-13: extract M266.024 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and close the original telescope as a Prop-valued definition
with a Statement suffix. Retain the arbitrary universe and NeZero degree
hypothesis. Import only the published subgroup, quotient definitions and
cardinality support. The source proof is reserved for a separate contribution.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U011.Definitions
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of an unramified valuation quotient: proposition target

Source: M266.024, lines 244–253 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- For nonzero degree, the valuation-divisibility quotient has that cardinality. -/
def unramifiedNormQuotient_card_eq_degreeStatement : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) [NeZero n],
    Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n

end Langlands.NYLL.LocalClassFieldTheory
