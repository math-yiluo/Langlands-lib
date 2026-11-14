/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 346, 14 November 2026: extract the types of M131.005,
M131.019 and M131.020 (PrincipalUnits.lean, lines 78–81, 186–193 and 199–203)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL and turn each theorem into a Prop-valued
definition with a Statement suffix whose parameters are the complete source
telescope and whose body is the source conclusion. Proofs are omitted and the
source import is replaced by the principal-unit quotient definitions.
See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.QuotientDefinitions

/-!
# Antitonicity, quotient induction and a unit identity: proposition targets

Prop-valued targets for the antitonicity of the principal-unit filtration,
elimination on the quotient `𝒪[K]ˣ ⧸ U^n` through representatives, and the
identity `ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)` for valuation-ring units.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

-- The source premise `h` does not occur in the conclusion; its name is kept.
set_option linter.unusedVariables false in
/-- Principal-unit groups decrease as the filtration index increases. -/
def principalUnits_antitoneStatement (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) : Prop :=
  principalUnits K n ≤ principalUnits K m

-- The source premise `h` does not occur in the conclusion; its name is kept.
set_option linter.unusedVariables false in
/-- Eliminate a quotient class through the canonical class map on arbitrary
representatives. -/
protected def IntegerUnitsPrincipalQuot.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsPrincipalQuot K n → Prop}
    (q : IntegerUnitsPrincipalQuot K n)
    (h : ∀ u : 𝒪[K]ˣ, motive (integerUnitsPrincipalQuotMk K n u)) : Prop :=
  motive q

/-- Algebra identity used to prove multiplicative closure of principal units. -/
def unit_mul_sub_one_eqStatement (K : Type u) [Field K] [ValuativeRel K]
    (a b : 𝒪[K]ˣ) : Prop :=
  ((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
    ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) +
      ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1)

end

end Langlands.NYLL.LocalFieldTheory
