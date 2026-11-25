/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.LocallySmall
public import Mathlib.CategoryTheory.Quotient.LocallySmall
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The derived category of a Grothendieck abelian category

Let `C` be an abelian category satisfying `IsGrothendieckAbelian.{w} C`. This file
constructs `HasDerivedCategory.{w} C`, i.e. a chosen localization of `CochainComplex C ℤ`
at the quasi-isomorphisms whose `Hom`-types live in `Type w`.

The construction is purely formal from the existence of K-injective resolutions
(`CategoryTheory.Abelian.HasKInjectiveResolutions`, which holds in every Grothendieck
abelian category by
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`):

* the homotopy category of complexes is locally `w`-small because the category of
  complexes is (`HomologicalComplex.locallySmall`) and quotients preserve local smallness;
* the full subcategory `HomotopyCategory.KInjectives C` is therefore locally `w`-small;
* by `HomotopyCategory.KInjectives.Qh.IsEquivalence` (assuming K-injective resolutions),
  it is equivalent to any model of the derived category, so `DerivedCategory C` is
  locally `w`-small;
* finally `MorphismProperty.hasLocalizationOfLocallySmall` shrinks the `Hom`-types of the
  standard derived category to `Type w`.

## Main definitions

* `DerivedCategory.locallySmall`: the derived category of a locally `w`-small abelian
  category with K-injective resolutions is locally `w`-small.
* `HasDerivedCategory.ofHasKInjectiveResolutions`: `HasDerivedCategory.{w} C` from
  `LocallySmall.{w} C` and `HasKInjectiveResolutions C`.
* `HasDerivedCategory.ofIsGrothendieckAbelian`: `HasDerivedCategory.{w} C` from
  `IsGrothendieckAbelian.{w} C`.

-/

@[expose] public section

universe w v u

open CategoryTheory Abelian

section HomotopyCategory

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

instance HomotopyCategory.locallySmall [LocallySmall.{w} V] [Small.{w} ι] :
    LocallySmall.{w} (HomotopyCategory V c) :=
  inferInstanceAs (LocallySmall.{w} (CategoryTheory.Quotient _))

end HomotopyCategory

variable (C : Type u) [Category.{v} C] [Abelian C]

instance DerivedCategory.locallySmall [LocallySmall.{w} C] [HasKInjectiveResolutions C]
    [HasDerivedCategory C] :
    LocallySmall.{w} (DerivedCategory C) :=
  (locallySmall_congr (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence).mp
    inferInstance

/-- If `C` is a locally `w`-small abelian category with K-injective resolutions, then the
localization of `CochainComplex C ℤ` at the quasi-isomorphisms can be constructed with
`Hom`-types in `Type w`. -/
@[implicit_reducible]
noncomputable def HasDerivedCategory.ofHasKInjectiveResolutions [LocallySmall.{w} C]
    [HasKInjectiveResolutions C] :
    HasDerivedCategory.{w} C :=
  letI : HasDerivedCategory.{max u v} C := HasDerivedCategory.standard C
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).hasLocalizationOfLocallySmall
    (DerivedCategory.Q (C := C))

/-- A Grothendieck abelian category `C` (relative to the universe `w`) has a derived
category with `Hom`-types in `Type w`. -/
@[implicit_reducible]
noncomputable instance HasDerivedCategory.ofIsGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    HasDerivedCategory.{w} C :=
  HasDerivedCategory.ofHasKInjectiveResolutions.{w} C
