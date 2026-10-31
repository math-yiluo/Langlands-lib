/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-30): extract only the proof of
   M248.002, `LocalFieldTheory.localCompleteDVFValuation_hasExtension`, from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
   namespace with Langlands.NYLL, state the theorem as the published closed
   proposition `LocalCompleteDVFValuationHasExtensionStatement` (so the
   binders are introduced by `intro`), and replace the original imports by the
   published statement module. The tactic proof is otherwise unchanged. The
   original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ExtensionStatement

/-!
# Extension compatibility of the canonical complete-DVF packages: proof

The canonical complete discrete valuations of two nonarchimedean local fields
preserve an existing extension of their canonical valuations.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The canonical complete-DVF packages preserve an existing extension of
the underlying valuative relations. -/
theorem localCompleteDVFValuation_hasExtension :
    LocalCompleteDVFValuationHasExtensionStatement.{u, v} := by
  intro K L _ _ _ _ _ _ _ _ _ _
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
  exact
    _root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) x

end Langlands.NYLL.LocalFieldTheory
