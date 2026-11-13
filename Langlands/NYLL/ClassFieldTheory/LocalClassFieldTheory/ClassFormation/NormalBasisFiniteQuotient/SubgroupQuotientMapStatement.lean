/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M148.003 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target,
-- prefix the namespace and reduce imports. See SubgroupQuotientMapStatement.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient.SubgroupQuotientMap

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open LocalFieldTheory
open scoped ValuativeRel

/-- The source surjectivity target for the subgroup quotient map. -/
def integerUnitsModPrincipalUnitsToSubgroupQuotient_surjectiveStatement
    (L : Type u) [Field L] [ValuativeRel L]
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) : Prop :=
  Function.Surjective
    (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h)

end

end Langlands.NYLL.LocalClassFieldTheory
