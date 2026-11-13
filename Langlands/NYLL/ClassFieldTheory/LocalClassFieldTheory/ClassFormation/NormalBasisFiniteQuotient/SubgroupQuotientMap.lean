/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M148.002 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
-- and reduce imports. See SubgroupQuotientMap.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open LocalFieldTheory CyclicCohomology
open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- The canonical map from `𝒪_Lˣ/U_L^m` onto `𝒪_Lˣ/V` whenever
`U_L^m ≤ V`. -/
def integerUnitsModPrincipalUnitsToSubgroupQuotient
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) :
    IntegerUnitsModPrincipalUnitsAtLevel L m →* (𝒪[L]ˣ ⧸ V) :=
  integerUnitsModPrincipalUnitsAtLevelLift m (QuotientGroup.mk' V)
    (by
      intro a ha
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk a : 𝒪[L]ˣ ⧸ V) = 1
      exact (QuotientGroup.eq_one_iff a).2 (h ha))

end

end Langlands.NYLL.LocalClassFieldTheory
