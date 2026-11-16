/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M154.002 from NYLL fbd320cd,
-- prefix the namespace and narrow imports. See the paired Markdown.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.PrincipalUnitSubgroupAction
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientDistribAction.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U109.U109.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

variable (K L : Type u)
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

/-- The actual action on `V^n` descends to the successive quotient
`V^n / V^(n+1)`. -/
@[implicit_reducible]
def chosenNormalBasisPrincipalUnitSuccQuotMulDistribMulAction
    (n : Nat) {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn)
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hVsucc : (Vsucc : Set 𝒪[L]ˣ) =
      chosenNormalBasisPrincipalUnitSet K L (n + 1)) :
    MulDistribMulAction (Gal(L / K))
      (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
    K L n Vn hVn
  change MulDistribMulAction (Gal(L / K))
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact quotientMulDistribMulActionOfSubgroupStable
    (Gal(L / K)) Vn
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) (by
      intro sigma a ha
      apply (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV (sigma • a)).2
      change (sigma • (a : 𝒪[L]ˣ)) ∈ (Vsucc : Set 𝒪[L]ˣ)
      rw [hVsucc]
      apply galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
        (K := K) (L := L) (n + 1) sigma
      rw [← hVsucc]
      exact (mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff
        (L := L) hV a).1 ha)

end

end Langlands.NYLL.LocalClassFieldTheory
