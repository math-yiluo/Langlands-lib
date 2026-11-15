/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the proof of M337.001 (lines
33–38) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace and opened namespace with Langlands.NYLL; import the
published Prop target and state the theorem as that target; replace the
unpublished CompleteDVF lemmas residue_eq_zero_iff (M107.019) and
uniformizer_mem_maximalIdeal (M107.023) by the Mathlib terms recorded in the
paired Markdown; replace the module documentation. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements

/-!
# A uniformizer reduces to zero

Exact proof of NYLL M337.001 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- A chosen uniformizer reduces to zero in the residue field. -/
theorem residueMap_uniformizer_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    residueMap_uniformizer_eq_zeroStatement hπ :=
  (IsLocalRing.residue_eq_zero_iff π).2
    ((Valuation.mem_maximalIdeal_iff (v := F.toCompleteDVF.valuation)).2
      hπ.val_lt_one)

end Langlands.NYLL.LubinTate.SameUniformizer
