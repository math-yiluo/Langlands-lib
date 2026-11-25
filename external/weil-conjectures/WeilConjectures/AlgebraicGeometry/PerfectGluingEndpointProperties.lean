/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Localized Mayer--Vietoris endpoint families

Source: Stacks Project, Tags 08BV and 08DR
(blueprint: def-perfect-gluing-endpoint-properties).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

noncomputable section

variable (Y : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ W : Y.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]

/-- Restrict to the localized site of an open and take derived direct image back.
This uses the actual right adjoint to restriction, not an unspecified witness.
Source: Stacks Project, Tag 08BV (blueprint: def-perfect-gluing-endpoint-properties). -/
def perfectGluingDirectImage (W : Y.Opens) :
    DerivedCategory (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W)) ⥤
      schemeDerivedCategory Y := by
  let R := moduleRings Y.toRingedSpace
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (R.over W)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      ((Opens.grothendieckTopology Y).over W)
      (Y.toRingedSpace.sheaf.over W)).1
  let L := SheafOfModules.overFunctor.{u} R W
  letI : L.IsLeftAdjoint := by
    dsimp [L, SheafOfModules.overFunctor]
    infer_instance
  let G := Functor.rightAdjoint L
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  exact G.rightDerivedFunctor

/-- Restrict to an open and take its derived direct image.
Source: Stacks Project, Tag 08BV (blueprint: def-perfect-gluing-endpoint-properties). -/
def perfectGluingLocalTerm (W : Y.Opens) :
    schemeDerivedCategory Y ⥤ schemeDerivedCategory Y :=
  (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) W).mapDerivedCategory ⋙
    perfectGluingDirectImage Y W

/-- Restrictions of perfect quasi-coherent objects to a localized open site.
Source: Step 2 of lem-pc-perfect-complexes-compact-set
(blueprint: def-perfect-gluing-endpoint-properties). -/
def perfectGluingRestrictionProperty (W : Y.Opens) :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))) :=
  fun Z ↦ ∃ E : schemeDerivedQCohCategory Y, IsPerfect Y E.obj ∧
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) W).mapDerivedCategory.obj E.obj ≅ Z)

/-- The possible middle terms in the two-open Mayer--Vietoris triangle.
Source: Stacks Project, Tag 08BV (blueprint: def-perfect-gluing-endpoint-properties). -/
def perfectGluingMiddleProperty (A B : Y.Opens) :
    ObjectProperty (schemeDerivedCategory Y) := fun Z ↦
  ∃ E : schemeDerivedQCohCategory Y, IsPerfect Y E.obj ∧
    Nonempty (((perfectGluingLocalTerm Y A).obj E.obj ⊞
      (perfectGluingLocalTerm Y B).obj E.obj) ≅ Z)

/-- The possible overlap terms in the two-open Mayer--Vietoris triangle.
Source: Stacks Project, Tag 08BV (blueprint: def-perfect-gluing-endpoint-properties). -/
def perfectGluingOverlapProperty (A B : Y.Opens) :
    ObjectProperty (schemeDerivedCategory Y) := fun Z ↦
  ∃ E : schemeDerivedQCohCategory Y, IsPerfect Y E.obj ∧
    Nonempty ((perfectGluingLocalTerm Y (A ⊓ B)).obj E.obj ≅ Z)

end

end AlgebraicGeometry.Scheme
