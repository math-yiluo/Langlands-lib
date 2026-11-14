/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 642 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, lines 1100–1108. Namespace and imports are adapted;
the theorem is typed against the published Prop target. The proof is unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.Statements

namespace Langlands.NYLL.CyclicCohomology

open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]

@[simp]
theorem mem_chosenNormalBasisPrincipalUnitSet_iff (n : Nat) (u : 𝒪[L]ˣ) :
    mem_chosenNormalBasisPrincipalUnitSet_iffStatement K L n u :=
  Iff.rfl

end Langlands.NYLL.CyclicCohomology
