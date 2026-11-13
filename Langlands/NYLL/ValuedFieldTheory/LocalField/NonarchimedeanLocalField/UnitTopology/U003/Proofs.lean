/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 127, 13 November 2026: prove M256.003 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean
at fbd320cd8b1b06487c58227e92eb135794267709 against the published target
localBaseUnitSubgroup_isOpenStatement; add Langlands.NYLL to the namespace,
import the published statement module, and inline the source's M256.002
membership argument as a local step of the openness proof.
LICENSE and NOTICE: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology.Statements

/-!
# Openness of the valuation-integer unit subgroup

The image of valuation-ring units in the unit group of a nonarchimedean local
field is open in the native topology on units.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The image of valuation-ring units is open in the native topology of a
nonarchimedean local field. -/
theorem localBaseUnitSubgroup_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localBaseUnitSubgroup_isOpenStatement K := by
  have hmem : ∀ x : Kˣ,
      x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1 := by
    intro x
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
  have hsphere : IsOpen {x : K | ValuativeRel.valuation K x = 1} := by
    simpa only [Valuation.restrict_eq_one_iff] using
      (ValuativeRel.valuation K).isOpen_sphere one_ne_zero
  have hpre := hsphere.preimage (Units.continuous_val :
    Continuous (fun x : Kˣ => (x : K)))
  unfold localBaseUnitSubgroup_isOpenStatement
  rw [show (localBaseUnitSubgroup K : Set Kˣ) =
      {x : Kˣ | ValuativeRel.valuation K (x : K) = 1} by
    ext x
    exact hmem x]
  exact hpre

end Langlands.NYLL.LocalFieldTheory
