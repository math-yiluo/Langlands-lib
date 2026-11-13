/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 202, 13 November 2026: extract the listed theorem types
from upstream fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package each complete source telescope as a Prop-valued
definition. Proofs and theorem attributes are omitted; imports are reduced
to the dependencies of the statements. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- Statement target for source unit M128.002. -/
def v_applyStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
    v K x =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
          ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
            ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Additive.toMul x).ne_zero)))

/-- Statement target for source unit M128.003. -/
def v_surjectiveStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Function.Surjective (v K)

/-- Statement target for source unit M128.004. -/
def v_mulStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ),
    v K (Additive.ofMul (x * y)) =
      v K (Additive.ofMul x) + v K (Additive.ofMul y)

/-- Statement target for source unit M128.005. -/
def v_oneStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    v K (Additive.ofMul (1 : Kˣ)) = 0

/-- Statement target for source unit M128.006. -/
def v_invStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ),
    v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)

/-- Statement target for source unit M128.019. -/
def v_integerUnitsToFieldUnitsStatement.{u} : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ),
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
