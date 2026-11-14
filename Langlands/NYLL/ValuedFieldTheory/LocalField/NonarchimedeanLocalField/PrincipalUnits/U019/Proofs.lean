/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 134, 14 November 2026: extract the proof of M131.019 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 188–199. Add the
Langlands.NYLL namespace prefix, give the theorem the published target
applied to its parameters as its type and import only
AntitoneQuotientStatements. The source tactic proof is unchanged. Omit the
source noncomputable section and all other source declarations. See the
paired Markdown; the original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements

/-!
# Induction on the quotient of valuation-ring units by principal units

A property of classes in `𝒪[K]ˣ ⧸ U^n` holds for every class once it holds
for the class of every valuation-ring unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Eliminate a quotient class through the canonical class map on arbitrary
representatives. -/
protected theorem IntegerUnitsPrincipalQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsPrincipalQuot K n → Prop}
    (q : IntegerUnitsPrincipalQuot K n)
    (h : ∀ u : 𝒪[K]ˣ, motive (integerUnitsPrincipalQuotMk K n u)) :
    IntegerUnitsPrincipalQuot.inductionOnStatement n (motive := motive) q h := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u

end Langlands.NYLL.LocalFieldTheory
