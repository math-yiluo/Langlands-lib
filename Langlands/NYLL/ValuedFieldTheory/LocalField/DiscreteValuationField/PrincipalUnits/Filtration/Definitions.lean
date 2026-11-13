/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# The higher principal-unit subgroup

Adapted by Worker 311 from NYLL M225.001 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix, isolate the construction, import the
published complete-DVF projections, and omit unused source opens/imports.
The subgroup definition and its closure proofs are unchanged.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The concrete `n`-th principal-unit subgroup of the valuation ring unit group. -/
def higherPrincipalUnitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup F.valuationSubringˣ where
  carrier := {u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}
  one_mem' := by
    change (1 : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [sub_self]
    exact (F.maximalIdeal ^ n).zero_mem
  mul_mem' := by
    intro x y hx hy
    have hxy :
        ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 =
          (x : F.valuationSubring) * ((y : F.valuationSubring) - 1) +
            ((x : F.valuationSubring) - 1) := by
      change (x : F.valuationSubring) * (y : F.valuationSubring) - 1 = _
      ring
    change ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxy]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) hx
  inv_mem' := by
    intro x hx
    have hxinv :
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
      calc
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) -
              ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
                (x : F.valuationSubring) := by
          rw [Units.inv_mul]
        _ = -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
          ring
    change ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxinv]
    exact (F.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left (F.maximalIdeal ^ n)
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) hx)


end DiscreteValuationField.CompleteDVF

end

end Langlands.NYLL.LocalFieldTheory
