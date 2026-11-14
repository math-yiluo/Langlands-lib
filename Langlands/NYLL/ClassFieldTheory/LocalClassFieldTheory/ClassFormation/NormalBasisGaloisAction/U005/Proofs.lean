/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 518, 14 November 2026: extract M145.005 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace, narrow imports,
and give the theorem its published target. Unfold principal-unit membership
and the unit action directly, using the published integer-ring evaluation law
instead of an unpublished unit-action rewriting lemma.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.PrincipalUnitStabilityStatement
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U004.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

theorem galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet
    (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (sigma : Gal(L/K)) {a : 𝒪[L]ˣ}
    (ha : a ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSetStatement K L n sigma ha := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  change ((((sigma • a : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  have hval : (((sigma • a : 𝒪[L]ˣ) : 𝒪[L]) : L) = sigma ((a : 𝒪[L]) : L) := by
    change ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L sigma (a : 𝒪[L]) :
      𝒪[L]) : L) = _
    exact galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L sigma (a : 𝒪[L])
  have hstable :=
    galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
      K L n sigma ha
  change sigma (((a : 𝒪[L]) : L) - 1) ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) at hstable
  change (((sigma • a : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1 ∈
    chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)
  simpa only [map_sub, map_one, hval] using hstable

end Langlands.NYLL.LocalClassFieldTheory
