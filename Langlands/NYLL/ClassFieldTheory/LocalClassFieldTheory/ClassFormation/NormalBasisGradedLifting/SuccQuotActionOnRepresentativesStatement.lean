/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract the exact M154.003 target from NYLL
-- fbd320cd as a Prop definition, prefix names and narrow imports.
-- See the paired Markdown for the complete source correspondence.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGradedLifting.PrincipalUnitSuccQuotAction

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u
open LocalFieldTheory CyclicCohomology
open scoped ValuativeRel

/-- States the theorem `chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mk`. -/
def chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction_smul_mkStatement
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
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1))
    (sigma : Gal(L/K)) (u : Vn) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  letI := chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    K L n hV hVn hVsucc
  sigma • chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u =
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV (sigma • u)

end

end Langlands.NYLL.LocalClassFieldTheory
