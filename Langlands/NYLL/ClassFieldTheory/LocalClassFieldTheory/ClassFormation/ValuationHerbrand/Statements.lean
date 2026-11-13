/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 13 November 2026: extract M142.001 from upstream
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, reduce imports, and represent the source theorem statement
as a Prop-valued definition. The source Type universes, full telescope,
finite-dimensionality omission and local action bindings are retained.
See the paired Markdown; LICENSE and NOTICE remain under licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [FiniteDimensional K L] in
def valuationHerbrand_shortExactStatement : Prop :=
    letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
    letI := galoisGroupFieldUnitsMulDistribMulAction K L
    letI := galoisGroupValueGroupMulDistribMulAction K L
    (∀ (σ : Gal(L / K)) (x : (ValuativeRel.valuation L).integerˣ),
        integerUnitsToFieldUnits L (σ • x) =
          σ • integerUnitsToFieldUnits L x) ∧
      (∀ (σ : Gal(L / K)) (x : Lˣ),
        valuationUnitsMulHom L (σ • x) =
          σ • valuationUnitsMulHom L x) ∧
      (∀ x : Lˣ, valuationUnitsMulHom L x = 1 ↔
        ∃ y : (ValuativeRel.valuation L).integerˣ,
          integerUnitsToFieldUnits L y = x) ∧
      Function.Injective (integerUnitsToFieldUnits L) ∧
      Function.Surjective (valuationUnitsMulHom L)

end
end Langlands.NYLL.LocalClassFieldTheory
