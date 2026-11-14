/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Statements

/-!
Modified by Worker 517: extract M146.007 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace/imports and
state the theorem through the published proposition. See Proofs.md.
-/

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory
open scoped ValuativeRel

universe u

protected theorem IntegerUnitsModPrincipalUnitsAtLevel.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement n q h := by
  unfold IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

end Langlands.NYLL.CyclicCohomology
