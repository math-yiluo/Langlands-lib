/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassMap
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassTopComparison
import WeilConjectures.AlgebraicGeometry.TargetSectionClassRestriction

/-! # Restriction compatibility of the local stalk class map

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

/-- The canonical stalk class of a global class agrees with the class computed using
an arbitrary supplied target resolution after restriction to the inverse-image open.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4) and Remark 20.14.2 (Tag 01FB).
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-restriction)

Proof: The top-comparison theorem identifies the defined class with the top-open
germ computed with the supplied resolution K. The fixed-resolution restriction
theorem identifies that same top-open germ with the germ of D.targetClass after
the cohomology restriction map. Transitivity combines the two equalities. -/
theorem localDirectImage_stalk_class_restriction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (I : InjectiveResolution F)
    (K : InjectiveResolution
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (V : Y.Opens) (hy : y ∈ V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (eta : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) :
    localDirectImage_stalk_class f y F p eta =
      TopCat.Presheaf.germ
            ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
              (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
                p).obj
                ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj
                  F))).presheaf V y hy (D.targetClass p
          (Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback
                (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p eta)) := by
  have htop := localDirectImage_stalk_class_top_comparison f y F p K eta
  have hrestriction := D.targetClass_restriction p y hy eta
  exact htop.trans hrestriction

end AlgebraicGeometry
