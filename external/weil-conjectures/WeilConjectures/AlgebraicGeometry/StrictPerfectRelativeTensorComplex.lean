/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # The explicit relative tensor complex on an open chart

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: def-pc-strict-perfect-relative-tensor-complex).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.module_overFunctor_preservesZero
  Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

/-- Restrict G to the open site, form the ordinary signed direct-sum total tensor
with L, and restrict scalars along the inverse-image structure-ring map on that site.
This construction makes no choice of a representative or of a quasi-isomorphism.
Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: def-pc-strict-perfect-relative-tensor-complex). -/
noncomputable def strictPerfectRelativeTensorComplex
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((TopCat.Sheaf.inverseImageRing f.base S.sheaf).over U))) ℤ := by
  letI : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  letI : (curriedTensor
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)
  letI (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M
  let GU := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
    (.up ℤ)).obj G
  let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
    (Modules.tensorPullbackRingMap f)
  let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).map α
  exact ((SheafOfModules.restrictScalars B).mapHomologicalComplex (.up ℤ)).obj
    (CochainComplex.mapBifunctor L GU
      (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
        (SheafOfModules.monoidalCategory (X.sheaf.over U))))

end AlgebraicGeometry.Scheme
