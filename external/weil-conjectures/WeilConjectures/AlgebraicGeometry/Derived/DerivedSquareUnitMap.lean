/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackTopCohomology
public import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleAdjunctionTranspose

/-! # The ordinary unit representative of a derived square

Source: Stacks Project, Cohomology, Tags 01FB and 08HY.
(blueprint: lem-weil-pbc-derived-square-unit-map).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w v
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback Adjunction.leftAdjointUniq
  Functor.rightDerivedFunctor pinnedModulePullbackComparisonAt

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The right-adjoint mate of the pinned pullback square, with its scalar normalization.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-derived-square-unit-map). -/
def derivedSquareRightComparison {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g) :
    schemeDerivedDirectImage v ⋙ schemeDerivedDirectImage f ≅
      schemeDerivedDirectImage k ⋙ schemeDerivedDirectImage g :=
  letI : ∀ {Y Y' : Scheme.{u}} (a : Y ⟶ Y'),
      (Scheme.Modules.tensorPullback a).Additive :=
    fun a ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} a
  conjugateIsoEquiv ((pinnedDerivedAdjunction f).comp (pinnedDerivedAdjunction v))
    ((pinnedDerivedAdjunction g).comp (pinnedDerivedAdjunction k))
    (pinnedPullbackComposition k g ≪≫
      eqToIso (congrArg (fun a ↦ derivedPullback a) h.symm) ≪≫
        (pinnedPullbackComposition v f).symm)

/-- Apply Rf to the ordinary coefficient map in degree zero and its direct-image unit,
then use the right-adjoint comparison of the square. This construction makes sense for
an arbitrary h-map and an arbitrary commutative square.
Source: Stacks Project, Tags 01FB and 08HY
(blueprint: lem-weil-pbc-derived-square-unit-map). -/
def derivedSquareUnitMap {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (F : X.Modules) (G : Z.Modules) (φ : F ⟶ (Scheme.Modules.pushforward v).obj G) :
    (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ⟶
    (schemeDerivedDirectImage g).obj ((schemeDerivedDirectImage k).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)) :=
  (schemeDerivedDirectImage f).map
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map φ ≫
          Scheme.Modules.canonicalSingleDirectImageMap v G) ≫
    (derivedSquareRightComparison f k g v h).hom.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G)

end AlgebraicGeometry
