/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

/-!
# Inverse image for possibly noncommutative pro-etale ring sheaves

## References

* Stacks Project, Tags 09A5, 00YV and 03D2
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The ring adjunction unit transported to the existing small site model.
No commutativity is used. -/
noncomputable def proEtaleRingModelUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R ⟶
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
        (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
            ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩

end AlgebraicGeometry.Scheme
