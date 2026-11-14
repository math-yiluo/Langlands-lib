/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.011 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 222-237, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import the published Valuation Statements
module and the published proof of v_integerUnitsToFieldUnits (M128.019), and
prove the published target applied to all its parameters. Since no proofs of
M140.010 and M134.029 are in the Library, both are proved as local facts by
their original proofs (Valuation.lean lines 213-220 and
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
ValuationExactSequence.lean lines 288-294). The latter inlines the original
proof of M134.020 (lines 182-205 there) and the original integer-unit
construction integerUnitOfValuationMapZero with its spec (lines 251-280),
with the integer membership criterion taken directly from Mathlib's
Valuation.mem_integer_iff and valuationMap_apply used through its
definitional equality. The proof then rewrites by the local M140.010 fact
and finishes as in the original.
Omit the source noncomputable section and all other source declarations.
See the paired Markdown; the original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs

/-!
# The kernel of the normalized valuation on field units

A field unit has normalized valuation `1` exactly when it comes from a unit
of the valuation integer ring.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- Exactness at `Lˣ`: the kernel of normalized valuation consists exactly
of the units of the valuation integer ring. -/
theorem valuationUnitsMulHom_eq_one_iff_exists_integerUnit
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) :
    valuationUnitsMulHom_eq_one_iff_exists_integerUnitStatement L x := by
  unfold valuationUnitsMulHom_eq_one_iff_exists_integerUnitStatement
  -- The source theorem M140.010 at `x`, proved by its original proof.
  have hOneIffZero :
      valuationUnitsMulHom L x = 1 ↔ valuationMap L (Additive.ofMul x) = 0 := by
    change valuationUnitsMulHom L x = 1 ↔
      Multiplicative.toAdd (valuationUnitsMulHom L x) = 0
    constructor
    · intro hx
      exact congrArg Multiplicative.toAdd hx
    · intro hx
      apply Multiplicative.toAdd.injective
      exact hx
  -- The source theorem M134.029, proved by its original proof.
  have hRange : ∀ y : Lˣ,
      y ∈ MonoidHom.range (integerUnitsToFieldUnits L) ↔
        valuationMap L (Additive.ofMul y) = 0 := by
    intro y
    constructor
    · rintro ⟨w, rfl⟩
      -- `valuationMap_apply` (M134.004) holds by `rfl`.
      change v L (Additive.ofMul (integerUnitsToFieldUnits L w)) = 0
      exact v_integerUnitsToFieldUnits L w
    · intro hy
      -- The source theorem M134.020 at `y`, proved by its original proof.
      have hv : ValuativeRel.valuation L (y : L) = 1 := by
        change v L (Additive.ofMul y) = 0 at hy
        dsimp [v] at hy
        have hunzero :
            WithZero.unzero
              (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)
                (ValuativeRel.valuation L (y : L)))
              ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)).2
                ((Valuation.ne_zero_iff (ValuativeRel.valuation L)).2 y.ne_zero)) =
              (1 : Multiplicative Int) := by
          have h := congrArg Multiplicative.ofAdd hy
          simpa using h
        apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).injective
        have hcoe :
            ((WithZero.unzero
              (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)
                (ValuativeRel.valuation L (y : L)))
              ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)).2
                ((Valuation.ne_zero_iff (ValuativeRel.valuation L)).2 y.ne_zero)) :
              Multiplicative Int) : WithZero (Multiplicative Int)) =
              (1 : WithZero (Multiplicative Int)) := by
          simpa using congrArg
            (fun z : Multiplicative Int => (z : WithZero (Multiplicative Int))) hunzero
        rw [WithZero.coe_unzero] at hcoe
        simpa using hcoe
      -- The source integer unit `integerUnitOfValuationMapZero L y hy`.
      let w : 𝒪[L]ˣ :=
        { val := ⟨(y : L), by
            rw [Valuation.mem_integer_iff]
            simp [hv]⟩
          inv := ⟨(y⁻¹ : L), by
            rw [Valuation.mem_integer_iff]
            simp [hv]⟩
          val_inv := by
            apply Subtype.ext
            change (y : L) * (y : L)⁻¹ = 1
            exact mul_inv_cancel₀ y.ne_zero
          inv_val := by
            apply Subtype.ext
            change (y : L)⁻¹ * (y : L) = 1
            exact inv_mul_cancel₀ y.ne_zero }
      -- The source theorem `integerUnitOfValuationMapZero_spec`.
      have hw : integerUnitsToFieldUnits L w = y := by
        ext
        rfl
      exact ⟨w, hw⟩
  rw [hOneIffZero]
  constructor
  · intro hx
    exact (hRange x).2 hx
  · rintro ⟨y, rfl⟩
    exact (hRange (integerUnitsToFieldUnits L y)).1 ⟨y, rfl⟩

end Langlands.NYLL.LocalClassFieldTheory
