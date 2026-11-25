/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Detecting exactness by maps into injective objects

In an abelian category with enough injectives, a short complex `S` is exact as soon as every
map `S.X₂ ⟶ J` into an injective object `J` that vanishes on `S.f` factors through `S.g`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

/-- A short complex is exact if `Hom(-, J)` sends it to an exact sequence for every injective
object `J`. -/
lemma exact_of_forall_injective (S : ShortComplex C)
    (h : ∀ (J : C) [Injective J] (φ : S.X₂ ⟶ J), S.f ≫ φ = 0 →
      ∃ ψ : S.X₃ ⟶ J, S.g ≫ ψ = φ) : S.Exact := by
  rw [S.exact_iff_epi_toCycles]
  let π := cokernel.π S.toCycles
  let ι := Injective.ι (cokernel S.toCycles)
  let φ := Injective.factorThru (π ≫ ι) S.iCycles
  have hφ : S.iCycles ≫ φ = π ≫ ι := Injective.comp_factorThru _ _
  obtain ⟨ψ, hψ⟩ := h _ φ (by
    rw [← S.toCycles_i, Category.assoc, hφ, ← Category.assoc, cokernel.condition,
      zero_comp])
  have hπ : π ≫ ι = 0 := by
    rw [← hφ, ← hψ, ← Category.assoc, S.iCycles_g, zero_comp]
  have : π = 0 := (cancel_mono ι).1 (by rw [hπ, zero_comp])
  exact Abelian.epi_of_cokernel_π_eq_zero _ this

end CategoryTheory.ShortComplex
