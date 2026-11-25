/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Ordinary tensor pullback and open restriction

Source: Stacks Project, Tags 0096, 0098 and 08DW.
(blueprint: def-pc-single-complex-open-tensor-restriction-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange

/-- Localize the literal ordinary pullback square and apply the exact restriction
factor. This is constructed on homotopy complexes, without a K-flatness hypothesis.
Source: Stacks Project, Tag 08DW.
(blueprint: def-pc-single-complex-open-tensor-restriction-iso). -/
noncomputable def singleComplexOpenTensorRestrictionMap
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : HasDerivedCategory.{w} X.Modules := d X
    letI : HasDerivedCategory.{w} X'.Modules := d X'
    letI : HasDerivedCategory.{w} U.toScheme.Modules := d U.toScheme
    letI : HasDerivedCategory.{w} U'.toScheme.Modules := d U'.toScheme
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    DerivedCategory.Q.{w}.obj (((Scheme.Modules.tensorPullback j).mapHomologicalComplex
      (.up ℤ)).obj (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)) ⟶
    (schemeOpenRestriction X' U').mapDerivedCategory.obj
      (DerivedCategory.Q.{w}.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) := by
  letI : HasDerivedCategory.{w} X.Modules := d X
  letI : HasDerivedCategory.{w} X'.Modules := d X'
  letI : HasDerivedCategory.{w} U.toScheme.Modules := d U.toScheme
  letI : HasDerivedCategory.{w} U'.toScheme.Modules := d U'.toScheme
  have : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
  have : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
  have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  have : (Scheme.Modules.tensorPullback g').Additive := tensorPullbackAdditive g'
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k => tensorPullbackAdditive k
  exact DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (openPinnedTensorRestrictionIso g' U U' j hj).inv (.up ℤ)).app P) ≫
    (schemeOpenRestriction X' U').mapDerivedCategoryFactors.inv.app _

end AlgebraicGeometry
