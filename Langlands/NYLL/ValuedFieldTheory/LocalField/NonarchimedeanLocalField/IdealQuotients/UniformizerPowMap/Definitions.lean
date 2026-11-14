/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 194 (2026-11-14): extract the listed M133 units
from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace/imports and theorem statements
as documented in the paired Markdown. Source construction bodies are retained.
Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U007.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U023.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.MaximalIdealDefinitions

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Source M133.018: exact proposition target. -/
def v_integerRingUniformizerFieldUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1

/-- Source M133.019: exact proposition target. -/
def v_inverseIntegerRingUniformizerFieldUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit K)) = 1

/-- Source M133.025: original construction. -/
def maximalIdealPowMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) where
  toFun r := ⟨r * ϖ ^ n, mul_uniformizer_pow_mem_maximalIdeal_pow K ϖ hϖ n r⟩
  map_add' r s := by
    ext
    simp [add_mul]
  map_smul' a r := by
    ext
    simp [mul_assoc]

/-- Source M133.027: original construction. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) :
    𝒪[K] →ₗ[𝒪[K]] MaximalIdealPowSuccQuot K n :=
  (maximalIdealPowSuccQuotMk K n).comp
    (maximalIdealPowMulUniformizerPowMap K ϖ hϖ n)

/-- Source M133.029: exact proposition target. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap_kerStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) : Prop :=
    LinearMap.ker (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n) =
      (𝓂[K] : Ideal 𝒪[K])

/-- Source M133.030: exact proposition target. -/
def maximalIdealPowSuccQuotMulUniformizerPowMap_surjectiveStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) : Prop :=
    Function.Surjective (maximalIdealPowSuccQuotMulUniformizerPowMap K ϖ hϖ n)

end

end Langlands.NYLL.LocalFieldTheory
