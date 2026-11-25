/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Descent of natural isomorphisms through derived open restriction

Source: Stacks Project, Tag 08BT, lemma-adjoint-lower-shriek-restrict;
Mathlib CategoryTheory.Localization.fullyFaithfulWhiskeringLeft.
(blueprint: lem-sc-derived-open-restriction-iso-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u w v z
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphisms descend through exact derived restriction to an open.
Source: Stacks Project, Tag 08BT, lemma-adjoint-lower-shriek-restrict;
Mathlib CategoryTheory.Localization.fullyFaithfulWhiskeringLeft.
(blueprint: lem-sc-derived-open-restriction-iso-descent).

Proof: Apply schemeDerivedOpenRestriction_isLocalization to the given open.
Precomposition with this localization is fully faithful by
Localization.fullyFaithfulWhiskeringLeft. Its preimageIso applied to alpha gives
beta, and map_preimage proves the asserted equality. The argument includes the
empty and whole opens and is independent of any union or overlap. -/
theorem derived_open_restriction_iso_descent
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    {E : Type z} [Category.{v} E]
    (F G : schemeDerivedCategory U.toScheme ⥤ E)
    (alpha : (schemeOpenRestriction X U).mapDerivedCategory ⋙ F ≅
      (schemeOpenRestriction X U).mapDerivedCategory ⋙ G) :
    ∃ beta : F ≅ G,
      Functor.isoWhiskerLeft (schemeOpenRestriction X U).mapDerivedCategory beta = alpha :=
  by
    let R := (schemeOpenRestriction X U).mapDerivedCategory
    let M := (MorphismProperty.isomorphisms _).inverseImage R
    let : R.IsLocalization M := schemeDerivedOpenRestriction_isLocalization X U
    let ff := Localization.fullyFaithfulWhiskeringLeft R M E
    refine ⟨ff.preimageIso alpha, ?_⟩
    ext H
    exact congrArg (fun f ↦ f.app H) (ff.map_preimage alpha.hom)

end AlgebraicGeometry.Scheme
