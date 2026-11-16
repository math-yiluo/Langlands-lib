/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M145.006 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See PrincipalUnitSubgroupAction.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.StableSubgroup
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U005.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L / K)) V := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact subgroupMulDistribMulActionOfStable (Gal(L / K)) 𝒪[L]ˣ V
    (by
      intro sigma a ha
      change sigma • (a : 𝒪[L]ˣ) ∈ (V : Set 𝒪[L]ˣ)
      rw [hV]
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma (hV ▸ ha))

end

end Langlands.NYLL.LocalClassFieldTheory
