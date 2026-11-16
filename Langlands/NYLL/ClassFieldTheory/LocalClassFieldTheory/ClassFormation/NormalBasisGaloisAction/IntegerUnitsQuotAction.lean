/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M145.010 from NYLL fbd320cd,
-- prefix the namespace and use published focused imports. See IntegerUnitsQuotAction.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientDistribAction.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U005.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The quotient action on `𝒪_Lˣ / V^n`, descended from the actual integer-unit
Galois action. -/
@[implicit_reducible]
def chosenNormalBasisIntegerUnitsQuotMulDistribMulAction
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) :
    MulDistribMulAction (Gal(L / K)) (𝒪[L]ˣ ⧸ V) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L / K)) 𝒪[L]ˣ V (by
      intro sigma a ha
      change a ∈ (V : Set 𝒪[L]ˣ) at ha
      change sigma • a ∈ (V : Set 𝒪[L]ˣ)
      rw [hV] at ha ⊢
      exact galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) n sigma ha)

end

end Langlands.NYLL.LocalClassFieldTheory
