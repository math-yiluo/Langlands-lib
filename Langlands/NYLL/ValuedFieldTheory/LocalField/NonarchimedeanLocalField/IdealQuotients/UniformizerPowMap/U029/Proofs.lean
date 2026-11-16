/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 642 (2026-11-16): extract M133.029 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace and imports,
state the theorem using its published Prop target, and expose named Prop targets
for the initial equality and the quotient-zero rewrite. The source proof route
is retained. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U069.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U024.Proofs

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The kernel of multiplication into the successive ideal quotient is the maximal ideal. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_ker
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    maximalIdealPowSuccQuotMulUniformizerPowMap_kerStatement K ϖ hϖ n := by
  change LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) =
    (𝓂[K] : Ideal 𝒪[K])
  ext r
  rw [LinearMap.mem_ker]
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) = 0 ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  rw [show maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) = 0 ↔
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r : 𝒪[K]) ∈
        (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) from
    maximalIdealPowSuccQuotMk_eq_zero_iff K n _]
  change r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
    r ∈ (𝓂[K] : Ideal 𝒪[K])
  exact mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff K ϖ hϖ n r

end Langlands.NYLL.LocalFieldTheory
