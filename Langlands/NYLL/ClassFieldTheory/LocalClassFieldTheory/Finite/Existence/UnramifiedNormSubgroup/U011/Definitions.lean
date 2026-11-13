/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract M266.011 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and import only the published valuation map definitions.
The subgroup definition and its proof fields are unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions

/-!
# The subgroup cut out by degree-divisibility of the valuation

This module adapts only M266.011, source lines 119–140 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The unramified norm subgroup of degree `n`: field units whose normalized
valuation lies in `nℤ`. -/
def unramifiedNormSubgroup (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) : Subgroup Kˣ where
  carrier := {x | (n : Int) ∣
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)}
  one_mem' := by
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (1 : Kˣ))
    rw [show Additive.ofMul (1 : Kˣ) = 0 by rfl, map_zero]
    exact dvd_zero (n : Int)
  mul_mem' := by
    intro x y hx hy
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul (x * y))
    rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y by rfl,
      map_add]
    exact dvd_add hx hy
  inv_mem' := by
    intro x hx
    change (n : Int) ∣
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x⁻¹)
    rw [show Additive.ofMul x⁻¹ = -Additive.ofMul x by rfl, map_neg]
    exact dvd_neg.mpr hx

end Langlands.NYLL.LocalClassFieldTheory
