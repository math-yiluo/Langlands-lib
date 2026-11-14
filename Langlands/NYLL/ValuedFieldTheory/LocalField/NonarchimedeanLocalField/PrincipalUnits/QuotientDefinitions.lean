/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 346, 14 November 2026: extract M131.008, M131.009 and
M131.011 (PrincipalUnits.lean, lines 96–107 and 118–122) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and replace the source import by the published principal-unit
definition with Mathlib's quotient groups. Declaration bodies are unchanged.
See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The quotient of valuation-ring units by a principal-unit subgroup

The type `𝒪[K]ˣ ⧸ U^n`, its commutative group structure and its canonical
quotient homomorphism, for every natural index `n`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Quotient of integer units by the actual principal-unit filtration. -/
def IntegerUnitsPrincipalQuot (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K n

/-- The quotient of valuation-ring units by an `n`-th principal-unit subgroup is a commutative
group. -/
instance integerUnitsPrincipalQuotCommGroup
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    CommGroup (IntegerUnitsPrincipalQuot K n) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)
  infer_instance

/-- The quotient map `𝒪[K]ˣ → 𝒪[K]ˣ/U^n`. -/
def integerUnitsPrincipalQuotMk (K : Type u) [Field K] [ValuativeRel K]
    (n : Nat) : 𝒪[K]ˣ →* IntegerUnitsPrincipalQuot K n := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)
  exact QuotientGroup.mk' (principalUnits K n)

end

end Langlands.NYLL.LocalFieldTheory
