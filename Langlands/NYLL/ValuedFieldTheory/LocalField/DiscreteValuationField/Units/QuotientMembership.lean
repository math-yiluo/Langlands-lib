/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.QuotientMembershipStatement

/-!
# Membership of a filtration image in a quotient

Adapted by Worker 311 from NYLL M120.082 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The theorem proves the
published statement using Mathlib's quotient comap/map formula and
the filtration's antitone law.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace DiscreteValuationField.AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- Source M120.082, proved against its published proposition. -/
theorem quotient_principalUnitSubgroup_mk_mem_classInQuotient_iff
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mk_mem_classInQuotient_iffStatement hmn x := by
  change x ∈ Subgroup.comap (QuotientGroup.mk' (U.principalUnitSubgroup n))
      (Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
        (U.principalUnitSubgroup m)) ↔ x ∈ U.principalUnitSubgroup m
  have hle : U.principalUnitSubgroup n ≤ U.principalUnitSubgroup m := U.antitone hmn
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hle]

end DiscreteValuationField.AntitoneSubgroupFiltration

end Langlands.NYLL.LocalFieldTheory
