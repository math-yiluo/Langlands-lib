/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract target M152.028 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See UniformizerGaloisStatement.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.UniformizerSubmodule

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

def chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_galoisGroupStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (τ : Gal(L/K)) : Prop :=
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]]
            chosenNormalBasisIntegerLattice K L) =
      chosenNormalBasisIntegerLatticeUniformizerSubmodule K L

end

end Langlands.NYLL.LocalClassFieldTheory
