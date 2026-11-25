/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.CategoryTheory.Localization.LocallySmall
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Derived localization universes on open subschemes

Source: Stacks Project, Tag 08FE; Mathlib, Localization/LocallySmall.
(blueprint: lem-pc-open-derived-category-small).
-/

@[expose] public section

universe u w
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An open subscheme admits a derived category in the same Hom universe as the ambient scheme.
Source: Stacks Project, Tag 08FE, derived restriction and direct image;
Mathlib, MorphismProperty.hasLocalizationOfLocallySmall.
(blueprint: lem-pc-open-derived-category-small).

Proof: first choose the standard derived category of modules on U. Open restriction
is exact and left adjoint to open direct image. Open direct image is fully faithful,
its counit being invertible, and preserves K-injective complexes because restriction
is exact. Its total right derived functor is therefore fully faithful. In particular,
it injects each Hom set of the standard D(U) into a Hom set of the fixed D(X), whose
morphisms live in universe w. Thus standard D(U) is locally w-small. Shrink its Hom
sets with MorphismProperty.hasLocalizationOfLocallySmall, retaining the localization
universal property. This constructs the requested localization; no arbitrary object
is chosen from a mere existence theorem. The argument includes the empty open. -/
theorem nonempty_openHasDerivedCategory (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
  let AU := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let := HasDerivedCategory.standard AU
  let L := schemeOpenRestriction X U
  let R := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let a : L ⊣ R := (Modules.restrictAdjunction U.ι).ofNatIsoLeft
    (Modules.overFunctorEquiv U).symm
  have : R.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : R.Full := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.full
  have : R.Faithful := (Modules.restrictAdjunction U.ι).fullyFaithfulROfIsIsoCounit.faithful
  have : LocallySmall.{w} (DerivedCategory AU) :=
    locallySmall_of_faithful R.rightDerivedFunctor
  exact ⟨(HomologicalComplex.quasiIso AU (.up ℤ)).hasLocalizationOfLocallySmall
    (DerivedCategory.Q (C := AU))⟩

end AlgebraicGeometry.Scheme
