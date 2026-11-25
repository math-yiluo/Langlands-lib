/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSinglePullbackSquare
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit

/-! # Degree-zero compatibility square for the canonical mate

Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-canonical-degree-zero-mate-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The standard degree-zero direct-image identification, computed by the existing
comparison of unbounded and bounded below derived functors.
Source: Stacks, Tags 079V and 0A1G
(blueprint: lem-pc-canonical-degree-zero-mate-square). -/
def canonicalDirectImageH0Iso {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≅
      (pushforward f).obj M :=
  (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).homologyRightDerivedFunctorObjSingleFunctorIso
      M 0 ≪≫
    (pushforward f).rightDerivedZeroIsoSelf.app M

end AlgebraicGeometry.Scheme.Modules
