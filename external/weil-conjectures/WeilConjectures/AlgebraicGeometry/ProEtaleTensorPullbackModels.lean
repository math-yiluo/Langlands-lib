/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

/-!
# Canonical tensor pullback on the small pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL (auxiliary; not a blueprint node).
The object universe of the site is u+1 and its morphism universe is u.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf
  CategoryTheory.tensorPullbackTotal CategoryTheory.tensorPullbackTotalComponent

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Bilinearity of the existing tensor on the small site with separate Hom universe.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: the four identities hold for sectionwise tensor maps on pure tensors. They pass
through module sheafification, yielding the four MonoidalPreadditive laws. -/
@[instance] theorem proEtaleTensorPreadditive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    @MonoidalPreadditive (proEtaleRingModules X R) _ _
      (SheafOfModules.monoidalCategory R) := by
  exact SheafOfModules.cochainModulesPreadditive R

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Compare the full generalized pairing with the sectionwise adjunction formula.
attribute [local semireducible] SheafOfModules.monoidalCategory

end AlgebraicGeometry.Scheme
