/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Localized derived pullback with independent universes

Source: Stacks Project, Tags 06YJ and 08DW; uniqueness of localization.
(blueprint: def-pc-localized-mixed-derived-pullback).
-/

@[expose] public section
set_option autoImplicit false
universe u wW wO
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport derived tensor pullback through canonical equivalences of localizations.
All objects and maps are constructed from localization and the existing derived pullback;
no witness of mere existence is chosen.
Source: Stacks Project, Tags 06YJ and 08DW.
(blueprint: def-pc-localized-mixed-derived-pullback). -/
noncomputable def localizedMixedDerivedPullback
    {S T : Scheme.{u}} (U : S.Opens) (V : U.toScheme.Opens) (W : T.Opens)
    (g : V.toScheme ⟶ W.toScheme)
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wO}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    DerivedCategory (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u}
        ((moduleRings U.toScheme.toRingedSpace).over V)) := by
  let QW := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let dW := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  letI := dW
  letI := dV
  let E := (Scheme.Modules.overEquiv V).inverse
  letI : E.Additive := Functor.additive_of_preserves_binary_products _
  exact (Localization.uniq QW (@DerivedCategory.Qh _ _ _ dW)
      (HomotopyCategory.quasiIso _ (.up ℤ))).functor ⋙
    @derivedPullback _ _ g dW dV ⋙
      @Functor.mapDerivedCategory _ _ _ dV _ _ _ _ E _ _ _

end AlgebraicGeometry
