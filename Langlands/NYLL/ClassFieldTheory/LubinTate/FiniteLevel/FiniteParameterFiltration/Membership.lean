/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the indicated units from NYLL
at pinned commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
namespace with Langlands.NYLL and use focused shared-interface imports.
Use Mathlib quotient subgroup correspondence and ideal-power inclusion
for the proof; see the paired Markdown for this replacement.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration.MembershipStatement
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- Membership in the finite parameter filtration, against the exact target. -/
theorem standardLubinTateUnitParameterClass_mem_subgroup_iff
    (F : LocalField.{u, v} K) (n k : ℕ) (hk : k ≤ n + 1)
    (u : F.valuationSubringˣ) :
    standardLubinTateUnitParameterClass_mem_subgroup_iffStatement F n k hk u := by
  have hle :
      higherPrincipalUnitGroup F.toCompleteDVF (n + 1) ≤
        higherPrincipalUnitGroup F.toCompleteDVF k := by
    intro a ha
    exact (Ideal.pow_le_pow_right hk) ha
  change u ∈
      Subgroup.comap
        (QuotientGroup.mk' (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)))
        (Subgroup.map
          (QuotientGroup.mk' (higherPrincipalUnitGroup F.toCompleteDVF (n + 1)))
          (higherPrincipalUnitGroup F.toCompleteDVF k)) ↔
    u ∈ higherPrincipalUnitGroup F.toCompleteDVF k
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr hle]

end Langlands.NYLL.LubinTate
