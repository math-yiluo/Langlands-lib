/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningAffineLocal
import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningAffineGlobalization

/-!
# Existence part of universal first order thickenings

The global gluing argument for formally unramified morphisms is isolated here.
(blueprint: lem-weil-pbc-universal-first-order-thickening-exists-existence)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A formally unramified morphism admits a universal first order thickening.
The proof is the affine-open construction and gluing argument of Stacks, More on
Morphisms, Lemma 37.7.1 (Tag 04F3): choose affine pieces, construct their
universal thickenings from the square-zero algebra construction, identify the
overlap thickenings by uniqueness, glue the pieces and verify the universal
lifting property locally. This is the existence conjunct split from the target
theorem so that the target can combine it with the independent uniqueness
argument. (blueprint: lem-weil-pbc-universal-first-order-thickening-exists-existence)
Proof: choose an affine open cover, apply the affine universal thickening
construction on each piece, identify overlap pieces by the uniqueness property,
glue the resulting schemes and maps, and check the lifting property on the
cover. -/
theorem FormallyUnramified.exists_universalFirstOrderThickening_existence
    {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h' := by
  obtain ⟨Z', i, h', hi, hcomp, haffine⟩ :=
    FormallyUnramified.exists_affine_local_universalFirstOrderThickening h
  exact ⟨Z', i, h', isUniversalFirstOrderThickening_of_affine_local
    h i h' hi hcomp haffine⟩

end AlgebraicGeometry
