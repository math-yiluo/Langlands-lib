/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 11 November 2026:
Extract M129.019 and M129.022 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and retain the source universes and telescopes. Replace the
source membership helper M129.009 by the published ValuativeExtension field
and Mathlib integrality lemmas. Inline the Mathlib multiplicativity and unit
identities used by M129.020–021 into the unit structure's inverse fields.
Use only the required published class and Mathlib imports. See paired Markdown.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension.Definitions
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.Integral

/-!
# The norm on valuation-ring units

The field norm of a valuation-ring unit, as an element and as a unit of the
base valuation ring, under the published integrality hypothesis.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]

/-- Defines `normIntegerUnitsValue`. -/
def normIntegerUnitsValue [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) : 𝒪[K] :=
  ⟨Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L),
    Valuation.Integers.mem_of_integral
      (Valuation.integer.integers (ValuativeRel.valuation K))
      (Algebra.isIntegral_norm K
        (LocalFieldTheory.ValuativeExtension.integer_isIntegral (x : 𝒪[L])))⟩

/-- Norm restricted to valuation-integer units. -/
def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [LocalFieldTheory.ValuativeExtension K L] : 𝒪[L]ˣ →* 𝒪[K]ˣ where
  toFun := fun x => {
    val := normIntegerUnitsValue (K := K) (L := L) x
    inv := normIntegerUnitsValue (K := K) (L := L) x⁻¹
    val_inv := by
      ext
      change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
        Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
      have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
          (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 :=
        congrArg (fun a : 𝒪[L]ˣ => ((a : 𝒪[L]) : L)) (mul_inv_cancel x)
      rw [← map_mul (Algebra.norm K), hx, map_one]
    inv_val := by
      ext
      change Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
        Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
      have hx : (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
          (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 :=
        congrArg (fun a : 𝒪[L]ˣ => ((a : 𝒪[L]) : L)) (inv_mul_cancel x)
      rw [← map_mul (Algebra.norm K), hx, map_one]
  }
  map_one' := by
    ext
    simp [normIntegerUnitsValue]
  map_mul' := by
    intro x y
    ext
    simp [normIntegerUnitsValue]

end IsNonarchimedeanLocalField

end
end Langlands.NYLL.LocalFieldTheory
