/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M152.015 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See CoordinateMapStatement.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.IntegerLatticeBasis
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.UniformizerSubmodule
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.CoordinateMaximalSubmodule

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel



def chosenNormalBasisIntegerLatticeUniformizerSubmodule_map_equivFunStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Prop :=
    (chosenNormalBasisIntegerLatticeUniformizerSubmodule K L).map
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun :
          chosenNormalBasisIntegerLattice K L →ₗ[𝒪[K]] (Gal(L / K) → 𝒪[K])) =
      chosenNormalBasisCoordinateMaximalSubmodule K L

end

end Langlands.NYLL.LocalClassFieldTheory
