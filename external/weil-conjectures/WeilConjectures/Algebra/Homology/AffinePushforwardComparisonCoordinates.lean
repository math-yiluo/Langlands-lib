/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine cohomology coordinates for a supplied ordinary comparison

Source: Stacks Project, Tags 01I9, 06Z0 and 0AVW.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
/-- The associated sheaf functor with the scheme-module category displayed.
Source: Stacks Project, Tag 01I9.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/
abbrev affinePushforwardTilde (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)

/-- The existing exact-tilde zero-map instance in displayed coordinates.
Source: Stacks Project, Tag 01I9.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/
@[instance] theorem affinePushforwardTilde_preservesZero (A : Type u) [CommRing A] :
    (affinePushforwardTilde A).PreservesZeroMorphisms :=
  affineBaseChangeTilde_preservesZero A

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Cohomology of the termwise ordinary comparison followed by the actual derived unit.
The ordinary comparison is an input; all other maps are the canonical exactness maps.
Source: Stacks Project, Tags 0AVW and 06Z0.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/
def affinePushforwardCohomologyMapOfComparison (A B : Type u) [CommRing A] [CommRing B]
    (φ : B →+* A)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ)))
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (affinePushforwardTilde B).obj ((ModuleCat.restrictScalars φ).obj (C.homology i)) ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
          (DerivedCategory.Q.obj
            (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))) := by
  let T := affinePushforwardTilde A
  let F := ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B
  let P : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
    Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))
  let : (affinePushforwardTilde B).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : (affinePushforwardTilde B).PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteLimits_of_preservesHomology (affinePushforwardTilde B)
  let : PreservesFiniteColimits (affinePushforwardTilde B) :=
    Functor.preservesFiniteColimits_of_preservesHomology (affinePushforwardTilde B)
  let : F.PreservesHomology := inferInstance
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : P.Additive := RingedSpace.moduleDirectImage_additive
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let D := (T.mapHomologicalComplex (.up ℤ)).obj C
  let a : (F.mapHomologicalComplex (.up ℤ)).obj C ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj D :=
    (σ.hom.mapHomologicalComplex (.up ℤ)).app C
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  let β := (RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit
  exact ((C.sc i).mapHomologyIso F).inv ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app
      ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
    H.map (DerivedCategory.Q.map a) ≫
    cast (by rfl) (H.map (β.app ((HomotopyCategory.quotient _ (.up ℤ)).obj D)))

/-- Cohomology coordinates from the tilde unit and exact homology comparisons.
Source: Stacks Project, Tags 01I9 and 06Z0.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/
def affinePushforwardRepresentativeCohomologyIso (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : schemeDerivedCategory (Spec (.of A)))
    (t : DerivedCategory.Q.obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L) (i : ℤ) :
    C.homology i ≅ (moduleSpecΓFunctor (R := .of A)).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i).obj L) := by
  let T := affinePushforwardTilde A
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : T.PreservesHomology := tilde_preservesHomology A
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  exact tilde.isoTop (R := .of A) (C.homology i) ≪≫
    (moduleSpecΓFunctor (R := .of A)).mapIso
      (((C.sc i).mapHomologyIso T).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          ((T.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫ H.mapIso t)

end AlgebraicGeometry
