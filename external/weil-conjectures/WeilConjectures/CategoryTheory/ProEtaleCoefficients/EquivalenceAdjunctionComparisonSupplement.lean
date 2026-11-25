/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison

/-! # Normalized adjunction comparisons across equivalences

Source: Stacks Project, Tags 0B65 and 0DV0; categorical extension used in the blueprint
`lemma-passing-schematic-closure--1`, Steps 1–2.
(blueprint: lem-sfb-equivalence-square-inverse-mate-coherence)

The three statements give the unique normalized comparison, its compatibility with
adjoint compositors, and the comparison of actual inverse mates. Diagram equalities
are stated at every object, equivalently as equalities of natural transformations.

## Main statements

- `exists_equivalenceAdjunctionComparison`: existence, uniqueness, Hom, unit and counit.
- `equivalenceAdjunctionComparison_compositor`: preservation of adjoint compositors.
- `equivalenceAdjunctionComparison_inverseMate`: inverse-mate equality and invertibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB uC vC uD vD uAb vAb uBb vBb uCb vCb uDb vDb

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {Ab : Type uAb} [Category.{vAb} Ab] {Bb : Type uBb} [Category.{vBb} Bb]
  {Cb : Type uCb} [Category.{vCb} Cb] {Db : Type uDb} [Category.{vDb} Db]



end CategoryTheory
