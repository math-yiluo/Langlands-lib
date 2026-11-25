/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# Congruence for the base change to the algebraic closure

The base change `φ̄ = φ × 𝟙` of a morphism `φ` over a field `k` to `k̄` only depends on `φ`, not
on the proof that it lies over `k` (`AlgebraicGeometry.Scheme.Hom.geometricFiberMap_congr`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The base change to `k̄` only depends on the morphism, not on the proof that it lies over
`k`. -/
lemma Scheme.Hom.geometricFiberMap_congr {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}}
    {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)} {φ φ' : X₀ ⟶ Y₀} (e : φ = φ')
    (h : φ ≫ g = f) (h' : φ' ≫ g = f) :
    Scheme.Hom.geometricFiberMap φ h = Scheme.Hom.geometricFiberMap φ' h' := by
  subst e
  rfl

end AlgebraicGeometry
