/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 532, 2026-11-14: extract M266.012 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and prove the exact closed Library Statement target.
Import only the published target; retain the original Iff.rfl proof
after introducing its universally quantified parameters.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.SubgroupStatements

/-!
# Membership in the unramified norm subgroup

Source: M266.012, lines 143–147 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Characterizes the unramified norm subgroup by divisibility of the normalized valuation. -/
theorem mem_unramifiedNormSubgroup_iff :
    mem_unramifiedNormSubgroup_iffStatement.{u} := by
  intro K _ _ _ _ n x
  exact Iff.rfl

end Langlands.NYLL.LocalClassFieldTheory
