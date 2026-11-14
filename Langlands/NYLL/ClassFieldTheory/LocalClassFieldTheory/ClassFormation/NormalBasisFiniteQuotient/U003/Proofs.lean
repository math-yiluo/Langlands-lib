/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 628: extract M148.003 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace,
-- reduce imports and prove the published Statement target. See Proofs.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient.SubgroupQuotientMapStatement

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

/-- The canonical map to a quotient by a larger subgroup is surjective. -/
theorem integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective
    (L : Type u) [Field L] [ValuativeRel L]
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    integerUnitsModPrincipalUnitsToSubgroupQuotient_surjectiveStatement L m V h := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  refine ⟨integerUnitsModPrincipalUnitsAtLevelMk L m a, ?_⟩
  rfl

end

end Langlands.NYLL.LocalClassFieldTheory
