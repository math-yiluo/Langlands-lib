/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the proof of M337.002 (lines
40–50) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace and opened namespace with Langlands.NYLL; import the
published Prop target and state the theorem as that target; replace the
unpublished CompleteDVF lemmas residue_eq_zero_iff (M107.019) and
maximalIdeal_eq_span_uniformizer (M107.024) by the Mathlib terms recorded in
the paired Markdown; replace the module documentation. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.Statements

/-!
# Zero residue implies divisibility by the uniformizer

Exact proof of NYLL M337.002 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- An element reducing to zero is divisible by the chosen uniformizer. -/
theorem uniformizer_dvd_of_residueMap_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {a : F.valuationSubring} (ha : F.residueMap a = 0) :
    uniformizer_dvd_of_residueMap_eq_zeroStatement hπ ha := by
  have hmem : a ∈ F.maximalIdeal :=
    (IsLocalRing.residue_eq_zero_iff a).1 ha
  have hspan :
      a ∈ Ideal.span ({π} : Set F.valuationSubring) := by
    simpa [Valuation.IsUniformizer.is_generator
      (v := F.toCompleteDVF.valuation) hπ] using hmem
  exact Ideal.mem_span_singleton.mp hspan

end Langlands.NYLL.LubinTate.SameUniformizer
