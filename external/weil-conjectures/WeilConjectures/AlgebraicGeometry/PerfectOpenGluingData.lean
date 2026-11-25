/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

/-! # Local data for gluing a perfect pullback comparison

Source: Stacks Project, Tag 09RF, the local data a, b, c before Tag 08DG.
(blueprint: def-pc-perfect-open-gluing-data).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 10000 in
-- Exact nested-open restriction needs a larger instance search budget.
/-- Two local perfect objects with compatible maps into Rg_*E whose local adjoints
are invertible. This is only local data: it contains no global object on Y.
The comparisons γ are part of the data and all morphisms are fixed explicitly.
Source: Stacks Project, Tag 09RF, the construction of a, b and c before gluing.
(blueprint: def-pc-perfect-open-gluing-data). -/
def PerfectOpenGluingData {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) : Prop :=
  ∃ (U V : Y.Opens), U ⊔ V = ⊤ ∧
  ∃ (adj : derivedPullback g ⊣ schemeDerivedDirectImage g)
    (γU : derivedPullback g ⋙ (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory ≅
      (schemeOpenRestriction Y U).mapDerivedCategory ⋙ derivedPullback (g ∣_ U))
    (γV : derivedPullback g ⋙ (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory ≅
      (schemeOpenRestriction Y V).mapDerivedCategory ⋙ derivedPullback (g ∣_ V))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (e : (schemeOpenOverlapRestriction Y
        (homOfLE (show U ⊓ V ≤ U from inf_le_left))).mapDerivedCategory.obj A ≅
      (schemeOpenOverlapRestriction Y
        (homOfLE (show U ⊓ V ≤ V from inf_le_right))).mapDerivedCategory.obj B)
    (a : A ⟶ (schemeOpenRestriction Y U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage g).obj E))
    (b : B ⟶ (schemeOpenRestriction Y V).mapDerivedCategory.obj
      ((schemeDerivedDirectImage g).obj E)),
    U.toScheme.IsPerfect A ∧ V.toScheme.IsPerfect B ∧
    (schemeOpenOverlapRestriction Y
        (homOfLE (show U ⊓ V ≤ U from inf_le_left))).mapDerivedCategory.map a ≫
        (schemeDerivedOpenRestrictionCompIso Y
          (homOfLE (show U ⊓ V ≤ U from inf_le_left))).hom.app
          ((schemeDerivedDirectImage g).obj E) =
      e.hom ≫
        (schemeOpenOverlapRestriction Y
          (homOfLE (show U ⊓ V ≤ V from inf_le_right))).mapDerivedCategory.map b ≫
        (schemeDerivedOpenRestrictionCompIso Y
          (homOfLE (show U ⊓ V ≤ V from inf_le_right))).hom.app
          ((schemeDerivedDirectImage g).obj E) ∧
    IsIso ((derivedPullback (g ∣_ U)).map a ≫
      γU.inv.app ((schemeDerivedDirectImage g).obj E) ≫
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.map (adj.counit.app E)) ∧
    IsIso ((derivedPullback (g ∣_ V)).map b ≫
      γV.inv.app ((schemeDerivedDirectImage g).obj E) ≫
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.map
        (adj.counit.app E))

end AlgebraicGeometry
