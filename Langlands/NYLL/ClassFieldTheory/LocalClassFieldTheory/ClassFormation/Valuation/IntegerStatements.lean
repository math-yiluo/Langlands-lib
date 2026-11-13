/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract M140.003, .004 and .007
from commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
with Langlands.NYLL, and import published dependencies. The theorem targets
are Prop-valued definitions with the Statement suffix. Data construction
bodies and local action scope are preserved. See the paired Markdown;
LICENSE and NOTICE are retained under licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

def galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    σ • x = Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x

def integerUnitsToFieldUnits_galoisGroup_equivariantStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (σ : Gal(L/K)) (x : 𝒪[L]ˣ) : Prop :=
    let _ : MulDistribMulAction (Gal(L / K)) 𝒪[L]ˣ :=
      galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    let _ : MulDistribMulAction (Gal(L / K)) Lˣ :=
      galoisGroupFieldUnitsMulDistribMulAction K L
    integerUnitsToFieldUnits L (σ • x) =
      σ • integerUnitsToFieldUnits L x

end
end Langlands.NYLL.LocalClassFieldTheory
