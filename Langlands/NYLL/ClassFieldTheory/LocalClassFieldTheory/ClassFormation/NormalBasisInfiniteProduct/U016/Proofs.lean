/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 519: extract M150.016 from NYLL fbd320cd,
-- prove the exact published target, and apply the closed-set limit theorem
-- directly after unfolding the principal-unit membership predicate.
-- See Proofs.md and licenses/NYLL/ for provenance and licensing.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProductLimitStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.U013.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section
universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter

theorem chosenNormalBasisPrincipalUnitCorrectionProduct_limit_mem
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (x : 𝒪[L]ˣ)
    (hx : Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) :
    chosenNormalBasisPrincipalUnitCorrectionProduct_limit_memStatement
      K L hclosed hmul z hz x hx := by
  have hxL : Tendsto
      (fun d : Nat =>
        (((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) : L))
      atTop (nhds ((((x : 𝒪[L]ˣ) : 𝒪[L])) : L)) :=
    (continuous_subtype_val.tendsto ((x : 𝒪[L]ˣ) : 𝒪[L])).comp hx
  have hsub : Tendsto
      (fun d : Nat =>
        (((((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]) - 1 : 𝒪[L]) : L)))
      atTop (nhds (((((x : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) := by
    simpa using hxL.sub (tendsto_const_nhds (x := (1 : L)))
  change ((((x : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  exact hclosed.mem_of_tendsto hsub
    (Eventually.of_forall (fun d =>
      chosenNormalBasisPrincipalUnitCorrectionProduct_mem K L hmul z hz d))

end
end Langlands.NYLL.LocalClassFieldTheory
