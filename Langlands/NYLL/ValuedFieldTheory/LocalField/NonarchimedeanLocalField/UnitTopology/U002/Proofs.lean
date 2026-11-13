/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 233, 13 November 2026: extract the proof of M256.002
from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean
at fbd320cd8b1b06487c58227e92eb135794267709; add Langlands.NYLL to the
namespace and opened inclusion-map namespace. Import the published Statements
module and state the theorem using its exact named proposition.
LICENSE and NOTICE: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.Statements

/-! # Valuation characterization of the valuation-integer unit subgroup -/

noncomputable section

universe u

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- A field unit lies in the image of valuation-ring units exactly when its
valuation is one. -/
theorem mem_localBaseUnitSubgroup_iff_valuation_eq_one
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) :
    mem_localBaseUnitSubgroup_iff_valuation_eq_oneStatement K x := by
  change x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1
  constructor
  · rintro ⟨a, rfl⟩
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) a)
  · intro hx
    let a : 𝒪[K]ˣ :=
      { val := ⟨(x : K), by
          rw [Valuation.mem_integer_iff]
          exact hx.le⟩
        inv := ⟨(x⁻¹ : K), by
          rw [Valuation.mem_integer_iff]
          simp [hx]⟩
        val_inv := by
          apply Subtype.ext
          change (x : K) * (x : K)⁻¹ = 1
          exact mul_inv_cancel₀ x.ne_zero
        inv_val := by
          apply Subtype.ext
          change (x : K)⁻¹ * (x : K) = 1
          exact inv_mul_cancel₀ x.ne_zero }
    exact ⟨a, by ext; rfl⟩

end Langlands.NYLL.LocalFieldTheory
