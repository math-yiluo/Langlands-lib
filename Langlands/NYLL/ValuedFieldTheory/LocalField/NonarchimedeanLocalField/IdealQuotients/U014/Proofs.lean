/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-13: extracted M133.014 from
IdealQuotients.lean at fbd320cd8b1b06487c58227e92eb135794267709; added Langlands.NYLL
and the exact named statement target. Local prerequisite adaptations and
private helpers are documented in the paired Markdown.
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Statements

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

private lemma withZeroMultiplicativeInt_le_of_lt_one
    (δ : WithZero (Multiplicative Int)) (hδ : δ < 1) :
    δ ≤ ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
      WithZero (Multiplicative Int)) := by
  cases δ using WithZero.recZeroCoe with
  | zero => exact bot_le
  | coe d =>
      rw [WithZero.coe_le_coe]
      rw [← Multiplicative.toAdd_le]
      change Multiplicative.toAdd d ≤ (-1 : Int)
      have hdlt : Multiplicative.toAdd d < (0 : Int) := by
        have h' : d < (1 : Multiplicative Int) := by
          simpa using hδ
        change Multiplicative.toAdd d < Multiplicative.toAdd (1 : Multiplicative Int)
        exact Multiplicative.toAdd_lt.mpr h'
      omega

private lemma withZeroMultiplicativeInt_maximal_lt_one_eq_ofAdd_neg_one
    {a : WithZero (Multiplicative Int)} (ha : a < 1)
    (hmax : ∀ δ : WithZero (Multiplicative Int), δ < 1 → δ ≤ a) :
    a = ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
      WithZero (Multiplicative Int)) := by
  apply le_antisymm
  · exact withZeroMultiplicativeInt_le_of_lt_one a ha
  · apply hmax
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    change (-1 : Int) < 0
    omega

private theorem valueGroupWithZeroIsoInt_eq_of_maximal_lt_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {a : ValuativeRel.ValueGroupWithZero K} (ha : a < 1)
    (hmax : ∀ δ : ValuativeRel.ValueGroupWithZero K, δ < 1 → δ ≤ a) :
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K a =
      ((Multiplicative.ofAdd (-1 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int)) := by
  let φ := _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply withZeroMultiplicativeInt_maximal_lt_one_eq_ofAdd_neg_one
  · simpa using φ.strictMono ha
  · intro δ hδ
    let ε : ValuativeRel.ValueGroupWithZero K := φ.symm δ
    have hε : ε < 1 := by
      have h := φ.symm.strictMono hδ
      simpa using h
    have hle : ε ≤ a := hmax ε hε
    have hle' := φ.strictMono.monotone hle
    dsimp [ε, φ] at hle'
    simpa using hle'
/-- Proof of the exact source-adapted M133.014 target. -/
theorem valueGroupWithZeroIsoInt_of_integerRing_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) :
    valueGroupWithZeroIsoInt_of_integerRing_irreducibleStatement K ϖ hϖ := by
  change _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (ValuativeRel.valuation K (ϖ : K)) = _
  apply valueGroupWithZeroIsoInt_eq_of_maximal_lt_one K
  · simpa using (Valuation.integer.v_irreducible_lt_one
      (v := ValuativeRel.valuation K) hϖ)
  · intro δ hδ
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := K) δ
    by_cases hx0 : x = 0
    · have hδ0 : δ = 0 := by
        simpa [hx0] using hx.symm
      rw [hδ0]
      exact bot_le
    · let y : 𝒪[K] := ⟨x, by
        change ValuativeRel.valuation K x ≤ 1
        rw [hx]
        exact le_of_lt hδ⟩
      have hylt : ValuativeRel.valuation K (y : K) < 1 := by
        change ValuativeRel.valuation K x < 1
        simpa [hx]
      have hynot : ¬ IsUnit y := by
        rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one
          (v := ValuativeRel.valuation K)]
        exact hylt
      have hym : y ∈ (𝓂[K] : Ideal 𝒪[K]) := by
        rw [IsLocalRing.mem_maximalIdeal]
        simpa [nonunits] using hynot
      have hyspan : y ∈
          (Ideal.span ({ϖ} : Set 𝒪[K]) : Ideal 𝒪[K]) := by
        simpa [hϖ.maximalIdeal_eq] using hym
      have hset := Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe
        (v := ValuativeRel.valuation K) ϖ
      have hyle : ValuativeRel.valuation K (y : K) ≤
          ValuativeRel.valuation K ((ϖ : 𝒪[K]) : K) := by
        have hyspanSet : y ∈
            ((Ideal.span ({ϖ} : Set 𝒪[K]) : Ideal 𝒪[K]) : Set 𝒪[K]) := hyspan
        rw [hset] at hyspanSet
        exact hyspanSet
      simpa [y, hx] using hyle

end Langlands.NYLL.LocalFieldTheory
