/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient

/-!
# Membership of a filtration image in a quotient

Adapted by Worker 311 from NYLL M120.082 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix; extract the proposition as a `Prop`-valued
definition with suffix `Statement`; rename its unused hypothesis `_hmn`; and
import the published shared filtration and quotient data.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace DiscreteValuationField.AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- Source M120.082: a representative lies in the image of level `m` in the
quotient by level `n` exactly when it lies in level `m`, provided `m ≤ n`. -/
def quotient_principalUnitSubgroup_mk_mem_classInQuotient_iffStatement
    {m n : ℕ} (_hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) : Prop :=
  QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
      U.principalUnitSubgroupClassInQuotient m n ↔
    x ∈ U.principalUnitSubgroup m

end DiscreteValuationField.AntitoneSubgroupFiltration

end Langlands.NYLL.LocalFieldTheory
