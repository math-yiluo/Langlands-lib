/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 628: extract M146.010 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace,
-- reduce imports and prove the published Statement target. See Proofs.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Statements

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- A unit represents the identity exactly when it lies in the level subgroup. -/
theorem integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement K n x := by
  change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K n) = 1 ↔ _
  exact QuotientGroup.eq_one_iff x

end

end Langlands.NYLL.CyclicCohomology
