/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 587 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- PrincipalUnits.lean, lines 54–57 and 73–76: conclusions are closed Prop targets,
-- and source proofs are omitted. See Statements.md and licenses/NYLL/.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

/-!
# Principal-unit membership and the zeroth subgroup

Closed proposition targets for the direct membership criterion at every natural
index and equality of the zeroth subgroup with all valuation-ring units.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The principal-unit membership criterion at every natural index. -/
def MemPrincipalUnitsIffStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] (a : 𝒪[K]ˣ) (n : Nat),
    a ∈ principalUnits K n ↔ ((a : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

/-- The zeroth principal-unit subgroup is all units of the valuation integer ring. -/
def PrincipalUnitsZeroStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K],
    principalUnits K 0 = (⊤ : Subgroup 𝒪[K]ˣ)

end Langlands.NYLL.LocalFieldTheory
