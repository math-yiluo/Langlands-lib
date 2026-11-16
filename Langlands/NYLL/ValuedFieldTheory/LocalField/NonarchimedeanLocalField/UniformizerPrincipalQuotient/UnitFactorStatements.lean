/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 330, 16 November 2026: extract only the theorem types
M376.002–.004 from UniformizerPrincipalQuotient.lean at source commit
fbd320cd8b1b06487c58227e92eb135794267709. Package each complete source
telescope as a closed Prop-valued definition, add the Langlands.NYLL namespace
prefix and Statement suffix, and make the source's arbitrary field universe
explicit. Replace source imports with the published definitions of the actual
unit-factor and integer-unit inclusion maps. Omit all source proofs and other
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U027.Definitions

/-!
# Unit-factor identity, product and integer-unit targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UniformizerPrincipalQuotient.lean`,
M376.002 (lines 36–41), M376.003 (49–57) and M376.004 (67–74).
NYLL's valuationMap is the negative of the usual normalized discrete order,
so the supplied valuation-one pi is an inverse uniformizer.
-/

open scoped ValuativeRel

namespace Langlands.NYLL.LocalFieldTheory

open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- M376.002: the unit factor of one is one. -/
def uniformizerUnitFactor_oneStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi 1 = 1

/-- M376.003: the unit factor preserves multiplication. -/
def uniformizerUnitFactor_mulStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1)
    (x y : Kˣ),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi (x * y) =
      IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi x *
        IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi y

/-- M376.004: the unit factor of an embedded integer unit recovers that unit. -/
def uniformizerUnitFactor_integerUnitStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (pi : Kˣ)
    (hpi : IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul pi) = 1)
    (u : 𝒪[K]ˣ),
    IsNonarchimedeanLocalField.uniformizerUnitFactor K pi hpi
        (integerUnitsToFieldUnits K u) = u

end Langlands.NYLL.LocalFieldTheory
