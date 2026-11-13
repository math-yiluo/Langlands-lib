/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 298, 2026-11-13.
Namespace prefix, focused imports and selected units; see paired Markdown.
-/
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions
import Mathlib.GroupTheory.QuotientGroup.Defs

noncomputable section
universe u v
namespace Langlands.NYLL.LubinTate
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
variable {K : Type u} [Field K]

/-- The finite unit parameters visible on the primitive level-`n + 1`
standard Lubin--Tate torsion point. -/
def standardLubinTateUnitParameter
    (F : LocalField.{u, v} K) (n : ℕ) : Type u :=
  F.valuationSubringˣ ⧸
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)

/-- The finite unit parameter quotient carries its canonical commutative
group structure. -/
instance standardLubinTateUnitParameter_commGroup
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommGroup (standardLubinTateUnitParameter F n) := by
  change CommGroup
    (F.valuationSubringˣ ⧸
      CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
  infer_instance

/-- The canonical class of a valuation-ring unit at primitive level
`n + 1`. -/
def standardLubinTateUnitParameterClass
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.valuationSubringˣ →* standardLubinTateUnitParameter F n :=
  QuotientGroup.mk'
    (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1))

/-- A chosen valuation-ring unit representing a finite unit parameter. -/
noncomputable def standardLubinTateUnitParameterChosenRepresentative
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : standardLubinTateUnitParameter F n) :
    F.valuationSubringˣ :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a)

end Langlands.NYLL.LubinTate
end
