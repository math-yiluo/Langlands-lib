/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Internal Hom under the lifted small-site equivalence

Source: Stacks 03D6 and 03EO, restriction to an equivalent site.
(blueprint: lem-sf-small-site-module-hom)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace SheafOfModules.SmallSite

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)

/-- The topology on the lifted small category.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
abbrev topology : GrothendieckTopology (AsSmall.{u + 1} C) :=
  AsSmall.down.{u, u + 1, u + 1}.inducedTopology J

/-- Lifting preserves the transported topology.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
instance up_continuous : AsSmall.up.{u, u + 1, u + 1}.IsContinuous J (topology J) := by
  have : AsSmall.up.{u, u + 1, u + 1}.IsDenseSubsite J (topology J) := by
    change (AsSmall.equiv.{u, u + 1, u + 1} : C ≌ AsSmall.{u + 1} C).functor.IsDenseSubsite J
      ((AsSmall.equiv.{u, u + 1, u + 1} : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J)
    infer_instance
  infer_instance

variable (R : Sheaf J CommRingCat.{u + 1})

/-- Restrict the coefficient sheaf without changing its sections.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
def coefficient : Sheaf (topology J) CommRingCat.{u + 1} :=
  (AsSmall.down.{u, u + 1, u + 1}.sheafPushforwardContinuous _ (topology J) J).obj R

/-- Module restriction along the inverse lift, from the small site to the original site.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
def restriction : SheafOfModules.{u + 1}
    ((sheafCompose (topology J)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficient J R)) ⥤
    SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
  pushforward (F := AsSmall.up.{u, u + 1, u + 1}) (𝟙 _)

/-- Both lift directions restrict modules and give inverse equivalences.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom).
The coefficient maps are identities. The lifted category's unit and counit have
identity underlying arrows, so the pushforward composition equations are identities. -/
def equivalence : SheafOfModules.{u + 1}
    ((sheafCompose (topology J)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficient J R)) ≌
    SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
  by
    have : (AsSmall.equiv.{u, u + 1, u + 1} : C ≌ AsSmall.{u + 1} C).functor.IsContinuous
        J (topology J) := up_continuous J
    have : (AsSmall.equiv.{u, u + 1, u + 1} : C ≌ AsSmall.{u + 1} C).inverse.IsContinuous
        (topology J) J := inferInstanceAs (AsSmall.down.{u, u + 1, u + 1}.IsContinuous _ _)
    exact pushforwardPushforwardEquivalence.{u + 1}
      (AsSmall.equiv.{u, u + 1, u + 1} : C ≌ AsSmall.{u + 1} C)
      (J := J) (K := topology J)
      (R := ((sheafCompose (topology J)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficient J R)))
      (S := ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
      (𝟙 _) (𝟙 _)
      (by
        ext U x
        change R.obj.map (𝟙 _) x = x
        exact ConcreteCategory.congr_hom (R.obj.map_id _) x)
      (by
        ext U x
        change R.obj.map (𝟙 _) x = x
        exact ConcreteCategory.congr_hom (R.obj.map_id _) x)

/-- The forward functor of the lifted equivalence is the specified restriction.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
theorem equivalence_functor : (equivalence J R).functor = restriction J R := rfl

/-- Restriction leaves addition of module maps unchanged.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
instance restriction_additive : (restriction J R).Additive where
  map_add := by intros; ext U x; rfl

/-- Modules on the lifted site.
Source: Stacks 03D6 (blueprint: lem-sf-small-site-module-hom). -/
abbrev SmallModules := SheafOfModules.{u + 1}
  ((sheafCompose (topology J) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficient J R))

/-- The sectionwise lift comparison.
Source: Stacks 03EO (blueprint: lem-sf-small-site-module-hom). -/
def unliftSliceMap (M N : SmallModules J R) (U : C)
    (f : (PresheafOfModules.restrictOver (coefficient J R).obj
        (AsSmall.up.{u, u + 1, u + 1}.obj U)).obj M.val ⟶
      (PresheafOfModules.restrictOver (coefficient J R).obj
        (AsSmall.up.{u, u + 1, u + 1}.obj U)).obj N.val) :
    (PresheafOfModules.restrictOver R.obj U).obj ((restriction J R).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj ((restriction J R).obj N).val where
  app W := f.app (op (Over.mk (AsSmall.up.{u, u + 1, u + 1}.map W.unop.hom)))
  naturality {W W'} i := by
    let j : Over.mk (AsSmall.up.{u, u + 1, u + 1}.map W'.unop.hom) ⟶
        Over.mk (AsSmall.up.{u, u + 1, u + 1}.map W.unop.hom) :=
      Over.homMk (AsSmall.up.{u, u + 1, u + 1}.map i.unop.left) (congrArg ULift.up (Over.w i.unop))
    exact f.naturality j.op

/-- The sectionwise lift comparison.
Source: Stacks 03EO (blueprint: lem-sf-small-site-module-hom). -/
def liftSliceMap (M N : SmallModules J R) (U : C)
    (f : (PresheafOfModules.restrictOver R.obj U).obj ((restriction J R).obj M).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj ((restriction J R).obj N).val) :
    (PresheafOfModules.restrictOver (coefficient J R).obj
        (AsSmall.up.{u, u + 1, u + 1}.obj U)).obj M.val ⟶
      (PresheafOfModules.restrictOver (coefficient J R).obj
        (AsSmall.up.{u, u + 1, u + 1}.obj U)).obj N.val where
  app W := f.app (op (Over.mk (AsSmall.down.{u, u + 1, u + 1}.map W.unop.hom)))
  naturality {W W'} i := by
    let j : Over.mk (AsSmall.down.{u, u + 1, u + 1}.map W'.unop.hom) ⟶
        Over.mk (AsSmall.down.{u, u + 1, u + 1}.map W.unop.hom) :=
      Over.homMk (AsSmall.down.{u, u + 1, u + 1}.map i.unop.left)
        (congrArg ULift.down (Over.w i.unop))
    exact f.naturality j.op

/-- The sectionwise lift comparison.
Source: Stacks 03EO (blueprint: lem-sf-small-site-module-hom). -/
def homApp (M N : SmallModules J R) (U : Cᵒᵖ) :
    ((restriction J R).obj (homObj (R := coefficient J R) M N)).val.obj U ≅
      (homObj (R := R) ((restriction J R).obj M) ((restriction J R).obj N)).val.obj U :=
  by
    let MS := (PresheafOfModules.restrictOver (coefficient J R).obj
      (AsSmall.up.{u, u + 1, u + 1}.obj U.unop)).obj M.val
    let NS := (PresheafOfModules.restrictOver (coefficient J R).obj
      (AsSmall.up.{u, u + 1, u + 1}.obj U.unop)).obj N.val
    let MO := (PresheafOfModules.restrictOver R.obj U.unop).obj ((restriction J R).obj M).val
    let NO := (PresheafOfModules.restrictOver R.obj U.unop).obj ((restriction J R).obj N).val
    letI : Module (R.obj.obj U) (MS ⟶ NS) := Module.compHom _
      ((PresheafOfModules.sectionsSMulHom NS).comp
        (PresheafOfModules.overSections (R := (coefficient J R).obj)
          (AsSmall.up.{u, u + 1, u + 1}.obj U.unop)))
    letI : Module (R.obj.obj U) (MO ⟶ NO) := Module.compHom _
      ((PresheafOfModules.sectionsSMulHom NO).comp
        (PresheafOfModules.overSections (R := R.obj) U.unop))
    exact LinearEquiv.toModuleIso (R := R.obj.obj U)
      { toFun := unliftSliceMap J R M N U.unop
        invFun := liftSliceMap J R M N U.unop
        left_inv := fun f ↦ by
          apply PresheafOfModules.hom_ext
          intro W
          ext x
          rfl
        right_inv := fun f ↦ by
          apply PresheafOfModules.hom_ext
          intro W
          ext x
          rfl
        map_add' := fun f g ↦ by
          apply PresheafOfModules.hom_ext
          intro W
          ext x
          rfl
        map_smul' := fun r f ↦ by
          apply PresheafOfModules.hom_ext
          intro W
          ext x
          rfl }

/-- Lifted slice maps and original slice maps have the same components. This identifies
internal Hom, naturally in both module variables.
Source: Stacks 03D6 and 03EO (blueprint: lem-sf-small-site-module-hom).
At U, send a map on the lifted slice to its components at the lifts of W -> U.
The inverse reads a map at the underlying arrows. These operations are inverse,
linear, and commute with every slice restriction and with composition. -/
def homIso (M N : SmallModules J R) :
    (restriction J R).obj (homObj (R := coefficient J R) M N) ≅
      homObj (R := R) ((restriction J R).obj M) ((restriction J R).obj N) :=
  (fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk (homApp J R M N)
    (fun _ _ _ ↦ by ext f; rfl)

/-- The internal Hom identification commutes with precomposition and postcomposition.
Source: Stacks 03EO (blueprint: lem-sf-small-site-module-hom). -/
theorem homIso_naturality {M M' N N' : SmallModules J R} (f : M' ⟶ M) (g : N ⟶ N') :
    (restriction J R).map (homObjMap (R := coefficient J R) f g) ≫
        (homIso J R M' N').hom =
      (homIso J R M N).hom ≫
        homObjMap (R := R) ((restriction J R).map f) ((restriction J R).map g) := by
  ext U h
  rfl

end SheafOfModules.SmallSite
