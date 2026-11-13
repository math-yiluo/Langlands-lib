/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract the specified M140
declarations from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace by Langlands.NYLL and reduce imports to the
published data used in the declarations. Theorems are represented by
Prop-valued definitions with the Statement suffix and unchanged statements.
Data construction bodies and their local instance scope are preserved.
See the paired Markdown; LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Mathlib.RingTheory.Valuation.Extension

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

def galoisGroupValueGroupMulDistribMulAction_smulStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (n : Multiplicative Int) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) (Multiplicative Int) :=
      galoisGroupValueGroupMulDistribMulAction K L
    σ • n = n

def valuationMap_unitsMapEquiv_galoisGroupStatement
    (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : Lˣ) : Prop :=
    valuationMap L
        (Additive.ofMul (Units.mapEquiv σ.toMulEquiv x)) =
      valuationMap L (Additive.ofMul x)

def valuationUnitsMulHom_galoisGroup_equivariantStatement
    (K L : Type u) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : Lˣ) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) Lˣ :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    let _ : MulDistribMulAction (Gal(L / K)) (Multiplicative Int) :=
      galoisGroupValueGroupMulDistribMulAction K L
    valuationUnitsMulHom L (σ • x) =
      σ • valuationUnitsMulHom L x

def valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zeroStatement
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) : Prop :=
    valuationUnitsMulHom L x = 1 ↔
      valuationMap L (Additive.ofMul x) = 0

def valuationUnitsMulHom_eq_one_iff_exists_integerUnitStatement
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) : Prop :=
    valuationUnitsMulHom L x = 1 ↔
      ∃ y : 𝒪[L]ˣ, integerUnitsToFieldUnits L y = x

def valuationUnitsMulHom_surjectiveStatement
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] : Prop :=
    Function.Surjective (valuationUnitsMulHom L)

end
end Langlands.NYLL.LocalClassFieldTheory
