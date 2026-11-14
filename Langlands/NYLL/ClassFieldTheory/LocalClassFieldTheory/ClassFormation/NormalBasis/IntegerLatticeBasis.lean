/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M152.002 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace and
-- use published focused imports. See IntegerLatticeBasis.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.U001.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def chosenNormalBasisIntegerLatticeBasis :
    Module.Basis Gal(L / K) 𝒪[K] (chosenNormalBasisIntegerLattice K L) :=
  ((IsGalois.normalBasis K L).restrictScalars 𝒪[K]).map
    (LinearEquiv.ofEq _ _
      (span_normalBasis_eq_chosenNormalBasisIntegerLattice K L))

end

end Langlands.NYLL.LocalClassFieldTheory
