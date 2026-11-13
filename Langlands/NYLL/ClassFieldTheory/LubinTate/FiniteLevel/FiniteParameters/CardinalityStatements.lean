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
variable {K : Type u} [Field K]

/-- M358.008: cardinality of the standard finite unit parameter quotient. -/
def standardLubinTateUnitParameter_natCardStatement
    (F : LocalField.{u, v} K) (n : ℕ) : Prop :=
  Nat.card (standardLubinTateUnitParameter F n) =
    (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n

end Langlands.NYLL.LubinTate
end
