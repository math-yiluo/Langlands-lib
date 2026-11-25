/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
public import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The flat base-change map on sections

Source: Stacks Project, Cohomology, Tags 02N7, 01E4 and 01FB
(blueprint: lem-weil-pbc-flat-base-change-map-sections).
-/

@[expose] public section

universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives


/-- Flat pullback preserves finite limits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
instance flatBaseChangePullbackLimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteLimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.1

/-- Flat pullback preserves finite colimits, from the recorded exactness theorem.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
instance flatBaseChangePullbackColimits {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    PreservesFiniteColimits (tensorPullback g) :=
  (flat_module_pullback_exact_pushforward_injective g).1.2

/-- Additivity follows from preservation of finite biproducts.
Source: Stacks, Tag 02N4 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
instance flatBaseChangePullbackAdditive {X Y : Scheme.{uBC}} (g : X ⟶ Y) [Flat g] :
    (tensorPullback g).Additive := Functor.additive_of_preserves_binary_products _

/-- The sectionwise comparison of the two composites of direct images in a square.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def flatBaseChangePushforwardSquare {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) :
    pushforward (pullback.snd g f) ⋙ pushforward f ≅
      pushforward (pullback.fst g f) ⋙ pushforward g :=
  pushforwardComp (pullback.snd g f) f ≪≫
    pushforwardCongr (pullback.condition (f := g) (g := f)).symm ≪≫
      (pushforwardComp (pullback.fst g f) g).symm

/-- Push the augmented lift down along f, and use the sectionwise square comparison.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def flatBaseChangeResolutionQ {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :
    ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
      ((pushforward g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (((pushforward (pullback.fst g f)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).map t ≫
    (NatIso.mapHomologicalComplex (flatBaseChangePushforwardSquare f g)
      (ComplexShape.up ℕ)).hom.app J.cocomplex

/-- The termwise adjoint c of q, with the canonical tensor-pullback adjunction.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def flatBaseChangeResolutionC {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) :=
  ((Classical.choose (exists_tensorPullbackAdjunction g)).mapHomologicalComplex
    (ComplexShape.up ℕ)).homEquiv _ _ |>.symm (flatBaseChangeResolutionQ f g I J t)

/-- H^p(c), with exact pullback's homology comparison and the resolution comparisons.
Source: Stacks, Tag 02N7 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def flatBaseChangeResolutionBeta {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶
      ((pushforward (pullback.snd g f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) :
    (tensorPullback g).obj (((pushforward f).rightDerived p).obj F) ⟶
      ((pushforward (pullback.fst g f)).rightDerived p).obj
        ((tensorPullback (pullback.snd g f)).obj F) :=
  (tensorPullback g).map (I.isoRightDerivedObj (pushforward f) p).hom ≫
    (((((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).sc p).mapHomologyIso (tensorPullback g)).inv ≫
    (HomologicalComplex.homologyFunctor S'.Modules (ComplexShape.up ℕ) p).map
      (flatBaseChangeResolutionC f g I J t) ≫
    (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv

/-- The canonical class map into R^p f_*F, using the restricted source resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def FlatBaseChangeOpenChoices.sourceClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.source.resolution
    (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    V D.source.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V

/-- The canonical class map into R^p f'_*F', using the restricted target resolution.
Source: Stacks, Tag 01E4 (blueprint: lem-weil-pbc-flat-base-change-map-sections).
(blueprint: def-weil-pbc-flat-base-change-resolution-construction)
-/
def FlatBaseChangeOpenChoices.targetClass {X S S' : Scheme.{uBC}}
    {f : X ⟶ S} {g : S' ⟶ S} {F : X.Modules} {I : InjectiveResolution F}
    {J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)} {V : S.Opens}
    (D : FlatBaseChangeOpenChoices f g F I J V) (p : ℕ) :=
  resolutionSectionClass D.target.resolution
    (((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (g ⁻¹ᵁ V) (D.target.sections ≪≫
      eqToIso (congrArg (fun U => ((RingedSpace.openModuleSections
        (Limits.pullback g f).toRingedSpace U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj J.cocomplex) (flatBaseChangeOpenEquality f g V))) p ≫
    Hom.app (J.isoRightDerivedObj (pushforward (pullback.fst g f)) p).inv (g ⁻¹ᵁ V)

end AlgebraicGeometry.Scheme.Modules
