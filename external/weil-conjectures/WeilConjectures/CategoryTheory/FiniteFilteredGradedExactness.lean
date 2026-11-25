/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Finite filtered graded exactness

Source: Stacks Project, Homology, Tag 05QH, lemma-filtered-acyclic,
parts (1)--(5), with the finite filtrations of Tag 0121
(blueprint: lem-trf-finite-filtered-graded-exactness).

The filtered objects, filtration-preserving maps, filtration steps, graded pieces and the
canonical step and graded maps are the recorded ones of `def-sp-filtration`
(`CategoryTheory.FilteredObject` over `CategoryTheory.DecreasingFiltration`, with
`WeilFilteredObject.restrictionSteps` and `WeilFilteredObject.gradedMapSteps`).

## Main definitions

- `CategoryTheory.FilteredObject.IsStrict`: strict filtered maps.
- `CategoryTheory.FilteredObject.quotientObject`, `CategoryTheory.FilteredObject.quotientMap`:
  the quotients `A/FᵖA` and the induced maps.

## Main statements

- `CategoryTheory.FilteredObject.finite_filtered_graded_exactness`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace WeilFilteredObject

/-- A filtered map `f : M → N` is strict when `f(FᵖM) = im(f) ∩ FᵖN` for every
integer `p`, as subobjects of `N`.
Source: Stacks Project, Homology, Tag 05QH, part (4)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
def IsStrict {A B : WeilFilteredObject C} (f : A ⟶ B) : Prop :=
  ∀ p : ℤ,
    imageSubobject (restrictionSteps f p ≫ (B.filtration.step p).arrow) =
      imageSubobject f.hom ⊓ B.filtration.step p

end WeilFilteredObject

end CategoryTheory
