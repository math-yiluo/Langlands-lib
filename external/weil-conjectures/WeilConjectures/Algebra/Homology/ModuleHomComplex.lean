/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # The module-valued total Hom complex

Source: Stacks Project, More on Algebra, Section 15.73, Tag 0A8H
(blueprint: def-sc-module-total-hom-complex).
The terms and differential are Mathlib's existing linear cochains and `δ_hom`.
-/

@[expose] public section

universe uH

open CategoryTheory

namespace CochainComplex

variable {A : Type uH} [CommRing A]

/-- The linear Hom differential has the prescribed shape.
Source: Stacks, Tag 0A8H (blueprint: def-sc-module-total-hom-complex).
Proof: Mathlib `HomComplex.δ_shape` says the differential vanishes off adjacent degrees. -/
theorem moduleHom_shape (L M : CochainComplex (ModuleCat.{uH} A) ℤ)
    (n m : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel n m) :
    ModuleCat.ofHom (HomComplex.δ_hom A L M n m) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact HomComplex.δ_shape n m h z

/-- Consecutive linear Hom differentials compose to zero.
Source: Stacks, Tag 0A8H (blueprint: def-sc-module-total-hom-complex).
Proof: Mathlib `HomComplex.δ_δ` proves this on every cochain; it is the cancellation of
mixed terms in `d_M f - (-1)^n f d_L`, with the remaining terms killed by `d² = 0`. -/
theorem moduleHom_square (L M : CochainComplex (ModuleCat.{uH} A) ℤ) (n m k : ℤ) :
    ModuleCat.ofHom (HomComplex.δ_hom A L M n m) ≫
      ModuleCat.ofHom (HomComplex.δ_hom A L M m k) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact HomComplex.δ_δ n m k z

/-- The A-module-valued Hom complex, using Mathlib's cochains and signed linear differential.
Source: Stacks, Tag 0A8H (blueprint: def-sc-module-total-hom-complex). -/
noncomputable def moduleHomComplex (L M : CochainComplex (ModuleCat.{uH} A) ℤ) :
    CochainComplex (ModuleCat.{uH} A) ℤ where
  X n := ModuleCat.of A (HomComplex.Cochain L M n)
  d n m := ModuleCat.ofHom (HomComplex.δ_hom A L M n m)
  shape := moduleHom_shape L M
  d_comp_d' n m k _ _ := moduleHom_square L M n m k

end CochainComplex
