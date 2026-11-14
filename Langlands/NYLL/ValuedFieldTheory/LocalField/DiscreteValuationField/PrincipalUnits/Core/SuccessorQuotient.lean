/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299 and Worker 478, 2026-11-13/14: extract NYLL units
M231.023–026 at commit fbd320cd8b1b06487c58227e92eb135794267709, prefix
namespaces with Langlands.NYLL, and import the published concrete subgroup
module. See the paired Markdown for all modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-!
# Successive principal-unit quotients

Adapted from NYLL M231.023–026,
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`,
lines 414–460, at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]
variable (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The adjacent quotient `U^n/U^(n+1)` for the concrete complete-DVF
principal-unit filtration. -/
def principalUnitSuccQuot (n : ℕ) : Type u :=
  higherPrincipalUnitGroup F n ⧸
    (higherPrincipalUnitGroup F (n + 1)).subgroupOf (higherPrincipalUnitGroup F n)

/--
Equips the target with its canonical `CommGroup` structure, namely `CommGroup
(higherPrincipalUnitGroup.principalUnitSuccQuot F n)`.
-/
instance principalUnitSuccQuotCommGroup (n : ℕ) :
    CommGroup (higherPrincipalUnitGroup.principalUnitSuccQuot F n) := by
  change CommGroup
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  infer_instance

/-- Explicit access to the concrete quotient used to implement
`principalUnitSuccQuot`. -/
def principalUnitSuccQuotConcreteEquiv (n : ℕ) :
    higherPrincipalUnitGroup.principalUnitSuccQuot F n ≃*
      (higherPrincipalUnitGroup F n ⧸
        (higherPrincipalUnitGroup F (n + 1)).subgroupOf
          (higherPrincipalUnitGroup F n)) := by
  change
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n)) ≃*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact MulEquiv.refl _

/-- The quotient map `U^n → U^n/U^(n+1)`. -/
def principalUnitSuccQuotMk (n : ℕ) :
    higherPrincipalUnitGroup F n →*
      higherPrincipalUnitGroup.principalUnitSuccQuot F n := by
  change higherPrincipalUnitGroup F n →*
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
  exact QuotientGroup.mk' ((higherPrincipalUnitGroup F (n + 1)).subgroupOf
    (higherPrincipalUnitGroup F n))

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end
