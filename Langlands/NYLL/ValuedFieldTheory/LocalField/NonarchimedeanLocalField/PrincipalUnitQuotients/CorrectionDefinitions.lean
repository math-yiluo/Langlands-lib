/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- Finite product of a correction sequence whose `d`-th term lies in
`U^(n+d)`. This algebraic partial product is the finite-stage input to the
complete-limit construction. -/
def principalUnitsCorrectionProduct (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) (z : ∀ d : Nat, principalUnits K (n + d)) :
    Nat → 𝒪[K]ˣ
  | 0 => 1
  | d + 1 => principalUnitsCorrectionProduct K n z d * (z d : 𝒪[K]ˣ)

end

end Langlands.NYLL.LocalFieldTheory
