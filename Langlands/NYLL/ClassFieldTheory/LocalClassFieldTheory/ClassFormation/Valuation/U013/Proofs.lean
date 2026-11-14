/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.013 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 251-262, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import the published Valuation Statements
module and the published proof of valuationMap_surjective (M134.005), and
prove the published target applied to all its parameters with the original
proof. Omit the source noncomputable section and all other source
declarations. See the paired Markdown; the original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs

/-!
# Surjectivity of the multiplicative normalized valuation

Every element of `Multiplicative ℤ` is the multiplicative normalized
valuation of some field unit.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

universe u

open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The multiplicative normalized valuation `Lˣ → Multiplicative ℤ` is
surjective. -/
theorem valuationUnitsMulHom_surjective
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] :
    valuationUnitsMulHom_surjectiveStatement L := by
  unfold valuationUnitsMulHom_surjectiveStatement
  intro n
  rcases valuationMap_surjective L (Multiplicative.toAdd n) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  change Multiplicative.ofAdd (valuationMap L x) = n
  rw [hx]
  rfl

end Langlands.NYLL.LocalClassFieldTheory
