/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.Statements

/-!
Modified by Worker 517: extract M144.115 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace/imports and
state the theorem through the published proposition. See Proofs.md.
-/

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

theorem chosenNormalBasisPrincipalUnitSuccQuotMk_surjective
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    chosenNormalBasisPrincipalUnitSuccQuotMk_surjectiveStatement L hV :=
  QuotientGroup.mk'_surjective
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

end Langlands.NYLL.CyclicCohomology
