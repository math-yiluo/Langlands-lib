/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.Statements

/-!
Modified by Worker 517: extract the M144.109 proof from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace and imports,
and state the theorem through its published Prop target. See Proofs.md.
-/

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

theorem mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) :
    mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iffStatement L hV u := by
  unfold mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iffStatement
  rw [chosenNormalBasisPrincipalUnitSuccSubgroup]
  exact Subgroup.mem_subgroupOf

end Langlands.NYLL.CyclicCohomology
