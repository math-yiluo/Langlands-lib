/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Supplement to the total complex file

Supplement to `Mathlib.Algebra.Homology.TotalComplex`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

This provides the lemmas `HomologicalComplex₂.total.map_add`,
`HomologicalComplex₂.total.map_zero` and `HomologicalComplex₂.total.isZero`.

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K L : HomologicalComplex₂ C c₁ c₂} (φ φ' : K ⟶ L)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  [K.HasTotal c₁₂] [L.HasTotal c₁₂]

namespace total

variable (K L) in
@[simp]
lemma map_add : map (φ + φ') c₁₂ = map φ c₁₂ + map φ' c₁₂ := by
  ext i₁₂ i₁ i₂ h
  simp [HomologicalComplex.add_f_apply]

variable (K L) in
@[simp]
lemma map_zero : map (0 : K ⟶ L) c₁₂ = 0 := by
  ext i₁₂ i₁ i₂ h
  simp

variable (K) in
lemma isZero (hK : IsZero K) : IsZero (K.total c₁₂) := by
  rw [IsZero.iff_id_eq_zero, ← map_id, hK.eq_of_src (𝟙 K) 0,
    map_zero]

end total

end HomologicalComplex₂
