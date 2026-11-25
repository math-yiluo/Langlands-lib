/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget

/-!
# Affineness of a thickening

Source: Stacks Project, More on Morphisms, Lemma 06AD (label
`lemma-thickening-affine-scheme`) (blueprint: lem-weil-pbc-thickening-affine-scheme).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A thickening of an affine scheme is affine. The proof applies Limits,
Proposition 05YU to the surjective universally closed closed immersion.
Source: Stacks Project, More on Morphisms, Lemma 06AD (label
`lemma-thickening-affine-scheme`) (blueprint: lem-weil-pbc-thickening-affine-scheme).
Proof: use the definition of `IsThickening` to obtain a surjective closed
immersion; closed immersions are universally closed, and Limits Proposition
05YU says that a scheme receiving such a morphism from an affine scheme is
affine (lem-weil-pbc-surjective-universally-closed-affine-target).
-/
theorem isAffine_of_isThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsThickening i) [IsAffine X] : IsAffine X' := by
  let : IsClosedImmersion i := hi.1
  let : Surjective i := hi.2
  exact isAffine_of_surjective_of_universallyClosed i

end AlgebraicGeometry
