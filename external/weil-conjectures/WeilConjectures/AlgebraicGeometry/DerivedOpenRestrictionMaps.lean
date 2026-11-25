/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Canonical derived restriction and its adjoint maps on opens

Source: Stacks Project, Cohomology, Tag 08BV
(blueprint: def-pc-derived-open-restriction-maps).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048

/-- Exact restriction from a scheme to an open subscheme.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
abbrev schemeOpenRestriction (X : Scheme.{u}) (U : X.Opens) :=
  (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (schemeOpenRestriction X U) :=
  comp_preservesFiniteLimits _ _

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_preservesFiniteColimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteColimits (schemeOpenRestriction X U) :=
  comp_preservesFiniteColimits _ _

/-- Additivity structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_additive (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Exact restriction between two open subschemes.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
abbrev schemeOpenOverlapRestriction (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :=
  (Equivalence.inverse
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U) ⋙
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
      (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv W))

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenOverlapRestriction_preservesFiniteLimits
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    PreservesFiniteLimits (schemeOpenOverlapRestriction X i) :=
  letI : PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
          (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv W)) := comp_preservesFiniteLimits _ _
  comp_preservesFiniteLimits _ _

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenOverlapRestriction_preservesFiniteColimits
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    PreservesFiniteColimits (schemeOpenOverlapRestriction X i) :=
  letI : PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
          (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv W)) := comp_preservesFiniteColimits _ _
  comp_preservesFiniteColimits _ _

set_option synthInstance.maxHeartbeats 400000 in
-- Zero preservation of the three-fold transported restriction needs more instance search.
/-- Additivity structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenOverlapRestriction_additive (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    (schemeOpenOverlapRestriction X i).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The canonical composition isomorphism for exact restriction to nested opens.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
def schemeOpenRestrictionCompIso (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U) :
    schemeOpenRestriction X U ⋙ schemeOpenOverlapRestriction X i ≅
      schemeOpenRestriction X W :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overEquiv U).unitIso.symm _ ≪≫
          Functor.leftUnitor _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
      (Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))
        (D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv W))

/-- Canonical composition isomorphism on the derived categories of nested opens.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
def schemeDerivedOpenRestrictionCompIso (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    : (schemeOpenRestriction X U).mapDerivedCategory ⋙
        (schemeOpenOverlapRestriction X i).mapDerivedCategory ≅
      (schemeOpenRestriction X W).mapDerivedCategory :=
  letI : PreservesFiniteLimits
      (schemeOpenRestriction X U ⋙ schemeOpenOverlapRestriction X i) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (schemeOpenRestriction X U ⋙ schemeOpenOverlapRestriction X i) :=
    comp_preservesFiniteColimits _ _
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (schemeOpenRestrictionCompIso X i)

/-- Restriction between derived direct images, defined as the adjoint of the
restriction counit, using the canonical composition isomorphism.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
def schemeDerivedOpenDirectImageRestriction
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι)
    (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage U.ι).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⟶
      (schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction X W).mapDerivedCategory.obj E) :=
  (adjW.homEquiv _ _)
    ((schemeDerivedOpenRestrictionCompIso X i).inv.app _ ≫
      (schemeOpenOverlapRestriction X i).mapDerivedCategory.map (adjU.counit.app _) ≫
        (schemeDerivedOpenRestrictionCompIso X i).hom.app E)

end AlgebraicGeometry
