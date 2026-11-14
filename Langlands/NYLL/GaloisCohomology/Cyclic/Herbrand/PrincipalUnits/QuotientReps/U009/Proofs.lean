/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 628: extract M146.009 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace,
-- reduce imports and prove the published Statement target. See Proofs.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Statements

namespace Langlands.NYLL.CyclicCohomology

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- A lifted homomorphism agrees with the original map on representatives. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAtLevelLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAtLevelLift_mkStatement n f h x :=
  rfl

end

end Langlands.NYLL.CyclicCohomology
