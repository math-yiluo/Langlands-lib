/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# Linearity of the shift functors on a full subcategory

If `C` is an `R`-linear category equipped with a shift by an additive monoid `A`, and
`P : ObjectProperty C` is stable under the shift, then the shift functors on the full
subcategory associated to `P` are `R`-linear if the shift functors on `C` are. This is the
`R`-linear analogue of the additivity instance of
`Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory.ObjectProperty

/-- The shift functors of a full subcategory stable under shifts are `R`-linear if those of
the ambient category are. -/
instance linear_shiftFunctor_fullSubcategory {R : Type*} [Ring R] {C : Type*} [Category* C]
    [Preadditive C] [Linear R C] (P : ObjectProperty C) {A : Type*} [AddMonoid A]
    [HasShift C A] [P.IsStableUnderShift A] (n : A) [(shiftFunctor C n).Linear R] :
    (shiftFunctor P.FullSubcategory n).Linear R where
  map_smul {X Y} f r := P.ι.map_injective <| by
    rw [← cancel_mono ((P.ι.commShiftIso n).hom.app Y), P.ι.commShiftIso_hom_naturality,
      Functor.map_smul, Functor.map_smul, Linear.comp_smul, Functor.map_smul, Linear.smul_comp,
      P.ι.commShiftIso_hom_naturality]

end CategoryTheory.ObjectProperty
