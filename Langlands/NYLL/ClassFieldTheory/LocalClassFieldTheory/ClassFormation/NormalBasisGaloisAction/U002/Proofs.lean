/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientActionStatement

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M145.002: Stable subgroup quotient action.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe uG uA

/-- A stable subgroup preserves the relation defining its quotient. -/
theorem quotientActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    quotientActionOfSubgroupStableStatement G A V hstable where
  inv_mul_mem g a b hab := by
    have hsmul : g • (a⁻¹ * b) ∈ V := hstable g (a⁻¹ * b) hab
    simpa [MulDistribMulAction.smul_mul, map_inv] using hsmul

end

end Langlands.NYLL.LocalClassFieldTheory
