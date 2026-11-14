/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 642 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, lines 1703–1710. Namespace and imports are adapted;
the theorem is typed against the published Prop target. See the paired Markdown
for proof modifications. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U091.Statements

namespace Langlands.NYLL.CyclicCohomology

open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

@[simp]
theorem mem_chosenNormalBasisLatticeSuccSubmodule_iff (n : Nat)
    (x : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)) :
    mem_chosenNormalBasisLatticeSuccSubmodule_iffStatement K L n x :=
  Iff.rfl

end Langlands.NYLL.CyclicCohomology
