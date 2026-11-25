/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Coherent comparison data for two open restrictions

Source: Stacks Project, Tags 08BV and 08DW.
(blueprint: def-pc-two-open-comparison-diagram).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/-- A pullback comparison diagram for two restrictions and their intersection.
All fields are actual functors, natural isomorphisms, or equations. In particular,
the two coherence equations concern functors, independently of any gluing object.
Source: Stacks Project, Tags 08BV and 08DW, restriction of derived pullback.
(blueprint: def-pc-two-open-comparison-diagram). -/
structure TwoOpenComparisonDiagram
    {C D A B W P Q T : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B]
    [Category* W] [Category* P] [Category* Q] [Category* T]
    (L : C ⥤ D) (TU : C ⥤ A) (TV : C ⥤ B) (TW : C ⥤ W)
    (SU : A ⥤ W) (SV : B ⥤ W)
    (RU : D ⥤ P) (RV : D ⥤ Q) (RW : D ⥤ T)
    (SP : P ⥤ T) (SQ : Q ⥤ T)
    (αU : TU ⋙ SU ≅ TW) (αV : TV ⋙ SV ≅ TW)
    (τU : RU ⋙ SP ≅ RW) (τV : RV ⋙ SQ ≅ RW) where
  /-- Pullback on the first open, transported to its localized site. -/
  HU : A ⥤ P
  /-- Pullback on the second open, transported to its localized site. -/
  HV : B ⥤ Q
  /-- Pullback on the intersection, transported to its localized site. -/
  HW : W ⥤ T
  /-- Pullback commutes with the first restriction. -/
  βU : L ⋙ RU ≅ TU ⋙ HU
  /-- Pullback commutes with the second restriction. -/
  βV : L ⋙ RV ≅ TV ⋙ HV
  /-- Pullback commutes with restriction to the intersection. -/
  βW : L ⋙ RW ≅ TW ⋙ HW
  /-- Pullback on the first open commutes with restriction to the intersection. -/
  γU : HU ⋙ SP ≅ SU ⋙ HW
  /-- Pullback on the second open commutes with restriction to the intersection. -/
  γV : HV ⋙ SQ ≅ SV ⋙ HW
  /-- The two first-open comparison paths coincide. -/
  coherenceU : ∀ F : C,
    τU.inv.app (L.obj F) ≫ SP.map (βU.hom.app F) ≫ γU.hom.app (TU.obj F) =
      βW.hom.app F ≫ HW.map (αU.inv.app F)
  /-- The two second-open comparison paths coincide. -/
  coherenceV : ∀ F : C,
    τV.inv.app (L.obj F) ≫ SQ.map (βV.hom.app F) ≫ γV.hom.app (TV.obj F) =
      βW.hom.app F ≫ HW.map (αV.inv.app F)

universe u w

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

/-- The two-open comparison diagram with its scheme and localized-site functors fixed.
The structure keeps the large exact-functor expressions behind one projection; no
comparison data is chosen in the definition.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-two-open-comparison-diagram). -/
structure SchemeTwoOpenComparisonDiagram
    (X Y : Scheme.{u}) (g : X ⟶ Y) (U V : Y.Opens) (P Q : X.Opens)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))] where
  /-- The actual simultaneous pullback comparison data. -/
  toDiagram :
    let SU : schemeDerivedCategory U.toScheme ⥤
        schemeDerivedCategory (U ⊓ V).toScheme := (schemeOpenOverlapRestriction Y
      (homOfLE (show U ⊓ V ≤ U from inf_le_left))).mapDerivedCategory
    let SV : schemeDerivedCategory V.toScheme ⥤
        schemeDerivedCategory (U ⊓ V).toScheme := (schemeOpenOverlapRestriction Y
      (homOfLE (show U ⊓ V ≤ V from inf_le_right))).mapDerivedCategory
    let TU : schemeDerivedCategory Y ⥤ schemeDerivedCategory U.toScheme :=
      (schemeOpenRestriction Y U).mapDerivedCategory
    let TV : schemeDerivedCategory Y ⥤ schemeDerivedCategory V.toScheme :=
      (schemeOpenRestriction Y V).mapDerivedCategory
    let TW : schemeDerivedCategory Y ⥤ schemeDerivedCategory (U ⊓ V).toScheme :=
      (schemeOpenRestriction Y (U ⊓ V)).mapDerivedCategory
    let αU : TU ⋙ SU ≅ TW := schemeDerivedOpenRestrictionCompIso Y
      (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    let αV : TV ⋙ SV ≅ TW := schemeDerivedOpenRestrictionCompIso Y
      (homOfLE (show U ⊓ V ≤ V from inf_le_right))
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P)
      |>.mapDerivedCategory
    let RV := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q)
      |>.mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (P ⊓ Q))
      |>.mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (show P ⊓ Q ≤ P from inf_le_left))).mapDerivedCategory
    let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (show P ⊓ Q ≤ Q from inf_le_right))).mapDerivedCategory
    let τU : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
        (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ P from inf_le_left)))
    let τV : RV ⋙ SQ ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
        (moduleRings X.toRingedSpace) (homOfLE (show P ⊓ Q ≤ Q from inf_le_right)))
    TwoOpenComparisonDiagram (derivedPullback g) TU TV TW SU SV
      RU RV RW SP SQ αU αV τU τV

end AlgebraicGeometry
