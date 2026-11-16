/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 642 (2026-11-16): extract M133.030 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace and imports,
state the theorem using its published Prop target, and expose named Prop targets
for surjectivity and the ideal-power rewrite. The source proof route is retained.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U062.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U021.Proofs

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Every successive ideal quotient class is a uniformizer power times an integer. -/
theorem maximalIdealPowSuccQuotMulUniformizerPowMap_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    maximalIdealPowSuccQuotMulUniformizerPowMap_surjectiveStatement K ϖ hϖ n := by
  change Function.Surjective (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n)
  intro x
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun x' =>
      ∃ r, maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n r = x')
    x ?_
  intro a
  have ha_span : (a : 𝒪[K]) ∈ Ideal.span ({ϖ ^ n} : Set 𝒪[K]) := by
    simpa [show (𝓂[K] ^ n : Ideal 𝒪[K]) = Ideal.span ({ϖ ^ n} : Set 𝒪[K]) from
      maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible K ϖ hϖ n] using a.2
  rcases (Ideal.mem_span_singleton.mp ha_span) with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  change maximalIdealPowSuccQuotMk K n
      (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r) =
    maximalIdealPowSuccQuotMk K n a
  have hrep : maximalIdealPowMulUniformizerPowMap K ϖ hϖ n r = a := by
    ext
    simp [maximalIdealPowMulUniformizerPowMap, hr, mul_comm]
  rw [hrep]

end Langlands.NYLL.LocalFieldTheory
