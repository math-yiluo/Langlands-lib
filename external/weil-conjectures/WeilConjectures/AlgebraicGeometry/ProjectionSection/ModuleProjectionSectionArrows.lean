/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical module projection and section comparisons

## References

* Stacks 07A4
* Stacks 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A typed alias of the existing total left derived pullback, keeping its inferred
K-flat structure fixed when using the tensor comparison. There is no new functor. -/
abbrev moduleDerivedPullback :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
        DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- A typed alias of the existing total right derived direct image, retaining its
canonical K-injective construction. There is no new functor. -/
abbrev moduleDerivedPushforward :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
        DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

namespace ProjectionSection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The left-ordered projection map is the adjunct of the canonical tensor comparison
followed by identity tensor the counit. -/
def projection {Z B : Scheme.{u}} (f : Z ⟶ B)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    M ⊗ (moduleDerivedPushforward Λ f).obj N ⟶
      (moduleDerivedPushforward Λ f).obj
        ((moduleDerivedPullback Λ f).obj M ⊗ N) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
    (((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app
      ((moduleDerivedPushforward Λ f).obj N) ≫
        (𝟙 ((moduleDerivedPullback Λ f).obj M) ⊗ₘ
          (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app N))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The canonical section pullback comparison, using the composition and
identity comparisons. -/
def pullbackSection {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X) :
    (moduleDerivedPullback Λ r) ⋙
      (moduleDerivedPullback Λ i) ≅ 𝟭 _ :=
  (CondensedRing.leftDerivedUpperStarComp Λ i r).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (eqToIso (congrArg (CondensedRing.upperStar Λ) h)) ≪≫
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X) ≪≫
    profinitePointModuleDerivedIdentity Λ X

end ProjectionSection

end AlgebraicGeometry.ProEtale
