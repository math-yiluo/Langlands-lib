/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 194 (2026-11-14): extract the listed M132 units
from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace/imports and theorem statements
as documented in the paired Markdown. Source construction bodies are retained.
Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U071.Proofs

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Source M132.072: original construction. -/
noncomputable def principalUnitOneAddOfMemPow
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : 𝒪[K]ˣ :=
  (isUnit_one_add_of_mem_maximalIdeal_pow K hn a ha).unit

/-- Source M132.073: exact proposition target. -/
def principalUnitOneAddOfMemPow_valStatement
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) : Prop :=
    ((principalUnitOneAddOfMemPow K hn a ha : 𝒪[K]ˣ) : 𝒪[K]) = 1 + a

end

end Langlands.NYLL.LocalFieldTheory
