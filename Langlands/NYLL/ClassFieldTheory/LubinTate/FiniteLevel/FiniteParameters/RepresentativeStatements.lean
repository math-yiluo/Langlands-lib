/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 298, 2026-11-13.
Namespace prefix, focused imports and selected units; see paired Markdown.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.Definitions

noncomputable section
universe u v
namespace Langlands.NYLL.LubinTate
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
variable {K : Type u} [Field K]

/-- M358.006: the chosen representative has the prescribed quotient class. -/
def standardLubinTateUnitParameterChosenRepresentative_specStatement
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) : Prop :=
  standardLubinTateUnitParameterClass F n
    (standardLubinTateUnitParameterChosenRepresentative F n a) = a

/-- M358.007: equality of classes is division-membership in the subgroup. -/
def standardLubinTateUnitParameterClass_eq_iff_div_memStatement
    (F : LocalField.{u, v} K) (n : ℕ)
    (a b : F.valuationSubringˣ) : Prop :=
  standardLubinTateUnitParameterClass F n a =
    standardLubinTateUnitParameterClass F n b ↔
      a / b ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)

end Langlands.NYLL.LubinTate
end
