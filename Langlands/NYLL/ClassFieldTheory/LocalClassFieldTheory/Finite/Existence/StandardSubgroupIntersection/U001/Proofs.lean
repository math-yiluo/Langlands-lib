/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 472, 14 November 2026: extract the proof of M403.001
(StandardSubgroupIntersection.lean, lines 45–83) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and prove the published closed proposition by introducing
its binders. The source support lemmas `valuationMap_ofMul_mul`,
`valuationMap_ofMul_zpow` and `mem_unramifiedNormSubgroup_iff` are replaced
by `map_add`, `map_zsmul` and the membership definition, and the source
imports by the published statement and the published proof of
`v_integerUnitsToFieldUnits`. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection.U001.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs

/-!
# Intersecting standard norm conditions: proof

Source: M403.001, lines 37–83 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

universe u

/-- The intersection of the unramified valuation condition and the
principal-unit condition is contained in the corresponding standard subgroup. -/
theorem unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le :
    unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_leStatement.{u} := by
  intro K _ _ _ _ ϖ d n hϖ x hx
  rcases Subgroup.mem_sup.mp hx.2 with ⟨y, hy, z, hz, hyz⟩
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hky⟩
  have hky' : ϖ ^ k = y := by
    simpa using hky
  change z ∈ (principalUnits K n).map (integerUnitsToFieldUnits K) at hz
  rcases hz with ⟨w, hw, hwz⟩
  have hvz : valuationMap K (Additive.ofMul z) = 0 := by
    rw [← hwz]
    exact v_integerUnitsToFieldUnits K w
  have hvx : valuationMap K (Additive.ofMul x) = k := by
    calc
      valuationMap K (Additive.ofMul x) =
          valuationMap K (Additive.ofMul y + Additive.ofMul z) := by
        rw [← hyz]
        rfl
      _ = valuationMap K (Additive.ofMul y) +
          valuationMap K (Additive.ofMul z) :=
        map_add _ _ _
      _ = valuationMap K (k • Additive.ofMul ϖ) + 0 := by
        rw [← hky', hvz, ofMul_zpow]
      _ = k * 1 + 0 := by
        rw [map_zsmul, hϖ, smul_eq_mul]
      _ = k := by
        rw [mul_one, add_zero]
  have hdk : (d : Int) ∣ k := by
    rw [← hvx]
    exact hx.1
  obtain ⟨t, ht⟩ := hdk
  have hyTarget : y ∈ Subgroup.zpowers (ϖ ^ d) := by
    rw [← hky', Subgroup.mem_zpowers_iff]
    refine ⟨t, ?_⟩
    calc
      (ϖ ^ d) ^ t = (ϖ ^ (d : Int)) ^ t := by
        rw [zpow_natCast]
      _ = ϖ ^ ((d : Int) * t) := by
        rw [zpow_mul]
      _ = ϖ ^ k := by
        rw [← ht]
  exact Subgroup.mem_sup.mpr ⟨y, hyTarget, z, ⟨w, hw, hwz⟩, hyz⟩

end Langlands.NYLL.LocalClassFieldTheory
