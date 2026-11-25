/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
import all WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantPullbackNative

/-! # Pullback of the constant scalar coefficient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedTensor upperStar lowerStar
  HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategorySingleFunctor
  singleFunctorCompLeftDerivedUpperStarIso leftDerivedUpperStarComp
  leftDerivedUpperStarCompactificationIso exceptionalConstantPullbackIso

private theorem step_four
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        (constantDerivedMap C c.g M) ≫ constantDerivedMap C c.i M ≫
        constantSingleHom C X M =
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor.map
          (constantSingleHom C Y M)) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).obj M)) ≫
      constantSingleMap C f M := by
  exact (step_one C c M).trans
    (congrArg (fun k ↦
      (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} C) c.g).leftDerivedFunctor.map
          (constantSingleHom C Y M)) ≫ k) (step_two C c M))

private theorem step_five
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        (constantDerivedMap C c.g M) ≫ constantDerivedMap C c.i M ≫
        constantSingleHom C X M =
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
        constantDerivedMap C f M ≫ constantSingleHom C X M := by
  exact (step_four C c M).trans (step_three C c M)

private theorem step_six
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
      (constantDerivedMap C c.g M) ≫ constantDerivedMap C c.i M =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
      constantDerivedMap C f M := by
  apply (cancel_mono (constantSingleHom C X M)).mp
  simpa only [Category.assoc] using step_five C c M

private theorem native_left_eq
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
      ((exceptionalConstantPullbackIso C c.g).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C c.i).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) =
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
      (constantDerivedMap C c.g M) ≫ constantDerivedMap C c.i M := by
  rfl

private theorem native_right_eq
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C f).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M) =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj M)) ≫
      constantDerivedMap C f M := by
  rfl

/-- Pullback of a constant complex concentrated in degree zero respects the
proper/open composition of a compactification.
Source: Stacks Tag 07A6; Zheng Construction 2.26
(blueprint: lem-pur-etale-constant-pullback-composition).

Proof: conjugate by the exact constant-sheaf/single comparison. On single
objects the derived composition comparison is the single of ordinary pullback
composition. Naturality of the single comparison moves the proper constant
identification through open pullback. The ordinary constant comparisons compose
by uniqueness of left adjoints, giving the claimed equality. -/
private theorem native_composition_complete
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((exceptionalConstantPullbackIso C c.g).hom.app ((DerivedCategory.singleFunctor
          (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C c.i).hom.app ((DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} C) 0).obj M) =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor
            (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} C) 0).obj M) := by
  exact (native_left_eq C c M).trans
    ((step_six C c M).trans (native_right_eq C c M).symm)

/-- Pullback of a constant complex concentrated in degree zero respects the
proper/open composition of a compactification.
Source: Stacks Tag 07A6; Zheng Construction 2.26
(blueprint: lem-pur-etale-constant-pullback-composition).

Proof: conjugate by the exact constant-sheaf/single comparison. On single
objects the derived composition comparison is the single of ordinary pullback
composition. Naturality of the single comparison moves the proper constant
identification through open pullback. The ordinary constant comparisons compose
by uniqueness of left adjoints, giving the claimed equality. -/
theorem etaleConstantPullback_comp_single
    (C : Type (u + 1)) [CommRing C] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : ModuleCat.{u + 1} C) :
    (upperStar (ModuleCat.{u + 1} C) c.i).leftDerivedFunctor.map
        ((exceptionalConstantPullbackIso C c.g).hom.app ((DerivedCategory.singleFunctor
          (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C c.i).hom.app ((DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} C) 0).obj M) =
    (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} C) c).hom.app
        ((constantSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} C)).mapDerivedCategory.obj ((DerivedCategory.singleFunctor
            (ModuleCat.{u + 1} C) 0).obj M)) ≫
      (exceptionalConstantPullbackIso C f).hom.app ((DerivedCategory.singleFunctor
        (ModuleCat.{u + 1} C) 0).obj M) := by
  exact native_composition_complete C c M

end AlgebraicGeometry.Etale
