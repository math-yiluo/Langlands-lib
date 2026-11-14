/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.Statements

/-!
Modified by Worker 517: extract M144.119 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace/imports and
use its published target. Apply the subgroup membership characterization
directly rather than importing the pending M144.109 proof. See Proofs.md.
-/

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

theorem chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iffStatement L hV u := by
  unfold chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iffStatement
  change
    (QuotientGroup.mk u :
      Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change u ∈ Vsucc.subgroupOf Vn ↔ (u : 𝒪[L]ˣ) ∈ Vsucc
  exact Subgroup.mem_subgroupOf

end Langlands.NYLL.CyclicCohomology
