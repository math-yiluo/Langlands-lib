/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the proof of M337.004 (lines
59–68) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace and opened namespace with Langlands.NYLL; import the
published Prop target and the M337.003 proof module and state the theorem as
that target; replace the unpublished CompleteDVF lemma
residue_ne_zero_iff_isUnit (M107.020) by IsLocalRing.residue_ne_zero_iff_isUnit;
replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U003.Proofs

/-!
# The factor `1 - π ^ r` is a unit

Exact proof of NYLL M337.004 against its published target.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- For positive `r`, the factor `1 - pi ^ r` is a unit of `O_K`. -/
theorem isUnit_one_sub_uniformizer_pow
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (hr : r ≠ 0) :
    isUnit_one_sub_uniformizer_powStatement hπ hr := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  intro hunit
  have hresidue_ne : F.residueMap (π ^ r) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (π ^ r)).2 hunit
  exact hresidue_ne (residueMap_uniformizer_pow_eq_zero hπ hr)

end Langlands.NYLL.LubinTate.SameUniformizer
