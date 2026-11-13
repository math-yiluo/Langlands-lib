/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 211 from pinned NYLL PrincipalUnitQuotients.lean.
-- See the paired Markdown for source lines, exact modifications and attribution.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open Filter

/-- Evaluation of the descended homomorphism on a representative. -/
def principalUnitsSuccQuotLift_mkStatement
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : principalUnits K n →* M)
    (h : (principalUnits K (n + 1)).subgroupOf
      (principalUnits K n) ≤ f.ker) (x : principalUnits K n) : Prop :=
  principalUnitsSuccQuotLift n f h
        (principalUnitsSuccQuotMk K n x) = f x

/-- Elimination of a class through the canonical quotient map. -/
protected def PrincipalUnitsSuccQuot.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : PrincipalUnitsSuccQuot K n → Prop}
    (q : PrincipalUnitsSuccQuot K n)
    (h : ∀ x : principalUnits K n,
      motive (principalUnitsSuccQuotMk K n x)) : Prop :=
  motive q

end

end Langlands.NYLL.LocalFieldTheory
