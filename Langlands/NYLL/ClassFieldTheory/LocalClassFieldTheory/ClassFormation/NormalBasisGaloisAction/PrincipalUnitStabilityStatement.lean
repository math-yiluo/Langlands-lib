/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract M145.005 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target.
-- The namespace, imports and effective theorem telescope are adapted; see the paired Markdown.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

set_option linter.unusedVariables false in
def galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSetStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (sigma : Gal(L/K)) {a : 𝒪[L]ˣ}
    (ha : a ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  sigma • a ∈ chosenNormalBasisPrincipalUnitSet K L n


end

end Langlands.NYLL.LocalClassFieldTheory
