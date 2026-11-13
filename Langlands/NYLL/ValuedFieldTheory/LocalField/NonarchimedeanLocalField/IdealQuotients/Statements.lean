/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 201 on 2026-11-13: extracted M133.005/.006/.014–016/.020–024
at source commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
definitions, preserving the source universes, ordered telescopes and targets.
Added Langlands.NYLL, qualified the Mathlib value-group isomorphism and reused
published NYLL v and the paired uniformizer definition. Original theorem proofs
are omitted. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The exact proposition of source unit M133.005; no proof is supplied here. -/
def chosenIntegerRingUniformizer_irreducibleStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    Irreducible (chosenIntegerRingUniformizer K)

/-- The exact proposition of source unit M133.006; no proof is supplied here. -/
def chosenIntegerRingUniformizer_maximalIdeal_eqStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop :=
    (𝓂[K] : Ideal 𝒪[K]) = Ideal.span ({chosenIntegerRingUniformizer K} : Set 𝒪[K])

/-- The exact proposition of source unit M133.014; no proof is supplied here. -/
def valueGroupWithZeroIsoInt_of_integerRing_irreducibleStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) : Prop :=
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K)) =
      ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int))

/-- The exact proposition of source unit M133.015; no proof is supplied here. -/
def v_integerRingIrreducibleFieldUnitStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K)) : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul u) = -1

/-- The exact proposition of source unit M133.016; no proof is supplied here. -/
def v_integerRingIrreducibleFieldUnit_invStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K)) : Prop :=
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul u⁻¹) = 1

/-- The exact proposition of source unit M133.020; no proof is supplied here. -/
def exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRingStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) : Prop :=
    ∃ n : Nat,
      (((chosenIntegerRingUniformizer K : 𝒪[K]) : K) ^ n) * x ∈ 𝒪[K]

/-- The exact proposition of source unit M133.021; no proof is supplied here. -/
def maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducibleStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) (n : Nat) : Prop :=
    (𝓂[K] ^ n : Ideal 𝒪[K]) = Ideal.span ({ϖ ^ n} : Set 𝒪[K])

/-- The exact proposition of source unit M133.022; no proof is supplied here. -/
def maximalIdeal_pow_eq_span_uniformizer_powStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) : Prop :=
    (𝓂[K] ^ n : Ideal 𝒪[K]) =
      Ideal.span ({chosenIntegerRingUniformizer K ^ n} : Set 𝒪[K])

/-- The exact proposition of source unit M133.023; no proof is supplied here. -/
def mul_uniformizer_pow_mem_maximalIdeal_powStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) : Prop :=
    r * ϖ ^ n ∈ (𝓂[K] ^ n : Ideal 𝒪[K])

/-- The exact proposition of source unit M133.024; no proof is supplied here. -/
def mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)
    (n : Nat) (r : 𝒪[K]) : Prop :=
    r * ϖ ^ n ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) ↔
      r ∈ (𝓂[K] : Ideal 𝒪[K])

end Langlands.NYLL.LocalFieldTheory
