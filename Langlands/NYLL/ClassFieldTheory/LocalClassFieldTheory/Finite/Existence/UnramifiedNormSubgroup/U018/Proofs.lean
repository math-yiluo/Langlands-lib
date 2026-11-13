/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 209, 2026-11-13: extract M266.018 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and prove the published closed proposition target.
Retain subgroup extensionality, unfold the published membership and
valuation-map definitions, and use Mathlib's integer-cast criterion.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.SubgroupStatements

/-!
# The unramified norm subgroup as a valuation kernel

This module proves the exact published target for M266.018.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The unramified norm subgroup is the kernel of the multiplicative reduced valuation. -/
theorem unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom :
    unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement.{u} := by
  intro K _ _ _ _ n
  ext x
  rw [MonoidHom.mem_ker]
  change
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) :
      ZMod n) = 0 ↔
    (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
  exact ZMod.intCast_zmod_eq_zero_iff_dvd
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)) n

end Langlands.NYLL.LocalClassFieldTheory
