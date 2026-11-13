/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M145.004 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target,
-- prefix the namespace and reduce imports. See LatticeStabilityStatement.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

set_option linter.unusedVariables false in
/-- The source target for Galois stability of a normal-basis lattice dilate. -/
def galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLatticeStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (sigma : Gal(L/K)) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) : Prop :=
  sigma x ∈ chosenBaseUniformizerPowSubmodule K L n
    (chosenNormalBasisIntegerLattice K L)

end

end Langlands.NYLL.LocalClassFieldTheory
