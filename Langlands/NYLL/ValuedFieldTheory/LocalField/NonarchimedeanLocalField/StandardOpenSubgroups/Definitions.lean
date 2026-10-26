/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
-- StandardOpenSubgroups.lean, lines 19–34, unfolding Basic.lean, lines 183–184.
-- See Definitions.md and licenses/NYLL/ for source correspondence and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Units.Hom

/-!
# Principal-unit subgroups of field units

The principal-unit subgroup of valuation-ring units is mapped into the field's
unit group by the canonical inclusion.
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

universe u

/-- The `n`-th principal-unit group, viewed as a subgroup of the field's
multiplicative group. -/
def fieldPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Subgroup Kˣ :=
  (principalUnits K n).map (Units.map (algebraMap 𝒪[K] K).toMonoidHom)

end Langlands.NYLL.LocalFieldTheory
