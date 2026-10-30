/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 384 (2026-10-29): extract only M247.004 from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
   namespace with Langlands.NYLL, and import the published complete-DVF
   definitions and native adic-completeness theorem through focused modules. -/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.CompleteProof

/-!
# Packaging a complete rank-one discrete valued field

The supplied valued-field data and the published native adic-completeness
theorem give a chosen `CompleteDVF` with the same value group and valuation.
-/

universe u v

namespace Langlands.NYLL.ValuationTheory.Valuations

open DiscreteValuationField

/-- A complete rank-one discrete valued field, equipped with its distinguished
valuation, gives a `CompleteDVF` by construction. -/
noncomputable def completeDVFOfCompleteValuedField
    {K : Type u} [Field K] {Gamma : Type v}
    [LinearOrderedCommGroupWithZero Gamma]
    [Valued K Gamma]
    [(Valued.v : _root_.Valuation K Gamma).IsRankOneDiscrete]
    [CompleteSpace K] :
    CompleteDVF.{u, v} K where
  ValueGroup := Gamma
  valuation := Valued.v
  instCompleteDiscrete :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := rankOneDiscreteValuationSubring_isAdicComplete }

end Langlands.NYLL.ValuationTheory.Valuations
