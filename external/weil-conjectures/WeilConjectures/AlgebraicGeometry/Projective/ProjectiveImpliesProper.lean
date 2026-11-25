/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective morphisms are proper

## References

* Stacks Project, Tag 01WC
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every (H-)projective morphism is proper. The other conjuncts record that projective-space
projections are proper, closed immersions are proper, and proper morphisms are closed under
composition. -/
theorem hProjective_properness :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsHProjective f → IsProper f) ∧
    (∀ (N : ℕ) (Y : Scheme.{u}),
      IsProper (ℙ(ULift.{u} (Fin (N + 1)); Y) ↘ Y)) ∧
    (∀ {X Y : Scheme.{u}} (i : X ⟶ Y), IsClosedImmersion i → IsProper i) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsProper f → IsProper g → IsProper (f ≫ g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y f hf
    have := hf
    exact IsHProjective.isProper f
  · intro N Y
    infer_instance
  · intro X Y i hi
    have := hi
    infer_instance
  · intro X Y Z f g hf hg
    have := hf
    have := hg
    infer_instance

end AlgebraicGeometry
