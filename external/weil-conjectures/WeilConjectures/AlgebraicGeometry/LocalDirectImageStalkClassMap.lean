/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Local direct-image stalks and total cohomology

Source: Stacks Project, Tags 02OD and 01E4.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- The canonical cohomology-to-stalk class map, before proving it invertible.
Source: Stacks Project, Tags 01E4 and 02OD.
(blueprint: def-weil-pbc-local-direct-image-stalk-class-map)

Use Mathlib's injective resolution of F', identify its global section complex with
the top sections of its direct-image complex, apply the canonical section class
map and the right-derived resolution comparison, and take the germ at y.
Every map is an existing construction; no existence theorem for an arbitrary
comparison equivalence supplies the data. -/
def localDirectImage_stalk_class {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) :
    (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F) →+
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))) :=
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let K := injectiveResolution F'
  let f' := pullback.fst (Y.fromSpecStalk y) f
  let L := ((Scheme.Modules.pushforward f').mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K.cocomplex
  ConcreteCategory.hom
    (Scheme.Modules.resolutionSectionClass K L ⊤ (Iso.refl _) p ≫
      Scheme.Modules.Hom.app (K.isoRightDerivedObj (Scheme.Modules.pushforward f') p).inv
        ⊤ ≫
      TopCat.Presheaf.germ
        ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
          (((Scheme.Modules.pushforward f').rightDerived p).obj F')).presheaf
        ⊤ y (by trivial))

end AlgebraicGeometry
