/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the proof of M337.003 (lines
52–57) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace and opened namespace with Langlands.NYLL; import the
published Prop target and the M337.001 proof module and state the theorem as
that target; name the M337.001 equation in a local hypothesis and add the
target definition to the source simp set; replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U001.Proofs

/-!
# Nonzero powers of a uniformizer reduce to zero

Exact proof of NYLL M337.003 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Every positive power of a uniformizer reduces to zero. -/
theorem residueMap_uniformizer_pow_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    residueMap_uniformizer_pow_eq_zeroStatement hπ hr := by
  have h0 : F.residueMap π = 0 := residueMap_uniformizer_eq_zero hπ
  simp [residueMap_uniformizer_pow_eq_zeroStatement, map_pow, h0, hr]

end Langlands.NYLL.LubinTate.SameUniformizer
