/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M152.008 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
-- and reduce imports. See UniformizerSubmodule.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The first uniformizer layer `π_K M`, regarded as a submodule of the
normal-basis lattice `M`. -/
def chosenNormalBasisIntegerLatticeUniformizerSubmodule :
    Submodule 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  (chosenBaseUniformizerPowSubmodule K L 1
      (chosenNormalBasisIntegerLattice K L)).comap
    (chosenNormalBasisIntegerLattice K L).subtype

end

end Langlands.NYLL.LocalClassFieldTheory
