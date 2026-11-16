/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract the target M152.005 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See MulPowBijectiveStatement.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

def chosenNormalBasisIntegerLatticeMulPowLinearMap_bijectiveStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) : Prop :=
    Function.Bijective (chosenNormalBasisIntegerLatticeMulPowLinearMap K L n)

end

end Langlands.NYLL.LocalClassFieldTheory
