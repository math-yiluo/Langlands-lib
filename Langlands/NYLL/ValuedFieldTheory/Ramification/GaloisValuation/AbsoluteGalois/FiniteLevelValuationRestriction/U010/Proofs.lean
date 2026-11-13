/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 256, with proof guidance by Worker 122 (2026-11-13):
   extract M233.010 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709,
   FiniteLevelValuationRestriction.lean lines 170-190, with Pointwise scope
   at line 150. Prefix the namespace with Langlands.NYLL, qualify Mathlib
   valuation names and introduce the published closed target telescope.
   Retain the original ring-of-integers proof and use the published
   Statements module instead of the upstream imports.
   Original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.Statements

namespace Langlands.NYLL.RamificationTheory.ValuationSubring

universe u v w

open scoped Pointwise in
/-- M233.010: a base-field automorphism preserves valuation extension. -/
theorem smul_hasExtension :
    smul_hasExtensionStatement.{u, v, w} := by
  intro K Ω _ _ _ Γ _ v A _ σ
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, _root_.ValuationSubring.integer_valuation,
    Valuation.mem_integer_iff, _root_.ValuationSubring.pointwise_smul_toSubring]
  rw [Subring.mem_pointwise_smul_iff_inv_smul_mem]
  have hcomm : (σ⁻¹) (algebraMap K Ω x) = algebraMap K Ω x :=
    (σ⁻¹).commutes x
  change (σ⁻¹) (algebraMap K Ω x) ∈ A.toSubring ↔ v x ≤ 1
  rw [hcomm]
  change (algebraMap K Ω x) ∈ A ↔ v x ≤ 1
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

end Langlands.NYLL.RamificationTheory.ValuationSubring
