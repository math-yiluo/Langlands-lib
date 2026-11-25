/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Ring and module inverse images at a topos point

Source: Stacks Project, Sites, Proposition 00YV; Modules on Sites, Section 03D2;
Cohomology on Sites, Tag 0DEN (auxiliary; not a blueprint node).

The operation graphs are tested on every sheaf T, including the products of operand
sheaves. They specify the finite-product transport, rather than an arbitrary lift.
No object is selected from an existence theorem: all data remain explicit in the
presentation, and the criterion will hold for every such presentation.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A presentation of the ring and module stalks at a point, with their induced
operations. The natural underlying-set isomorphism fixes the maps as well as the
objects. Testing operation graphs on product sheaves specifies exactly transport
by the inverse finite-product comparison; constants use the terminal sheaf.
Source: Stacks 00YV and 03D2 (auxiliary; not a blueprint node). -/
structure RingedSitePoint
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (p : GeometricMorphism (Type w) (Sheaf J (Type w))) where
  ring : CommRingCat.{w}
  ringUnderlying : p.inverse.obj ((sheafCompose J (forget CommRingCat.{w})).obj R) ≅
    (forget CommRingCat.{w}).obj ring
  ringAdd : ∀ (T : Sheaf J (Type w))
    (a b t : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) +
          (@id ring (ringUnderlying.hom (p.inverse.map b x)))
  ringMul : ∀ (T : Sheaf J (Type w))
    (a b t : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) *
          (@id ring (ringUnderlying.hom (p.inverse.map b x)))
  ringZero : ∀ (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map a x))) = 0
  ringOne : ∀ (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ x : p.inverse.obj T,
      (@id ring (ringUnderlying.hom (p.inverse.map a x))) = 1
  modules : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤ ModuleCat.{w} ring
  moduleUnderlying : modules ⋙ forget (ModuleCat.{w} ring) ≅
    (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat.{w})) ⋙ p.inverse
  moduleAdd : ∀ (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a b t : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (M.val.obj U) (a.hom.app U x)) + (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map t x))) =
        (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map a x))) +
          (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map b x)))
  moduleZero : ∀ (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (M.val.obj U) (a.hom.app U x)) = 0) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map a x))) = 0
  moduleSMul : ∀ (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (T : Sheaf J (Type w)) (a : T ⟶ ((sheafCompose J (forget CommRingCat.{w})).obj R))
    (b t : T ⟶ ((SheafOfModules.toSheaf _ ⋙ sheafCompose J
      (forget AddCommGrpCat.{w})).obj M)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (M.val.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) • (@id (M.val.obj U) (b.hom.app U x))) →
    ∀ x : p.inverse.obj T,
      (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map t x))) =
        (@id ring (ringUnderlying.hom (p.inverse.map a x))) •
          (@id (modules.obj M) ((moduleUnderlying.inv.app M) (p.inverse.map b x)))
  modules_additive : modules.Additive

attribute [instance] RingedSitePoint.modules_additive

namespace PointTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory CartesianMonoidalCategory
open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}

private noncomputable abbrev rset (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget CommRingCat.{w})).obj R

private noncomputable abbrev base (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R

private noncomputable abbrev mset (R : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.toSheaf (base R) ⋙ sheafCompose J (forget AddCommGrpCat.{w})

variable (F : Sheaf J (Type w) ⥤ Type w)

omit [EssentiallySmall.{w} C] in
private theorem eval_binary [F.Monoidal] {X Y Z T : Sheaf J (Type w)}
    (o : X ⊗ Y ⟶ Z) (a : T ⟶ X) (b : T ⟶ Y) (t : T ⟶ Z)
    (h : t = lift a b ≫ o) (x : F.obj T) :
    F.map t x = F.map o (μ F X Y (F.map a x, F.map b x)) := by
  rw [h, F.map_comp, ← Functor.Monoidal.lift_μ]
  rfl

omit [EssentiallySmall.{w} C] in
private theorem eval_constant [F.Monoidal] {Z T : Sheaf J (Type w)}
    (o : 𝟙_ (Sheaf J (Type w)) ⟶ Z) (t : T ⟶ Z)
    (h : t = toUnit T ≫ o) (x : F.obj T) :
    F.map t x = F.map o (ε F PUnit.unit) := by
  rw [h, F.map_comp, ← Functor.Monoidal.toUnit_ε]
  rfl

omit [EssentiallySmall.{w} C] in
private theorem eval_unary [F.Monoidal] {X Y T : Sheaf J (Type w)}
    (o : X ⟶ Y) (a : T ⟶ X) (t : T ⟶ Y) (h : t = a ≫ o) (x : F.obj T) :
    F.map t x = F.map o (F.map a x) := by
  rw [h, F.map_comp]
  rfl

-- Any two stalk elements have a simultaneous generalized representative on a product sheaf.
omit [EssentiallySmall.{w} C] in
private theorem all₂ [F.Monoidal] {X Y : Sheaf J (Type w)} (P : F.obj X → F.obj Y → Prop)
    (h : ∀ (T : Sheaf J (Type w)) (a : T ⟶ X) (b : T ⟶ Y)
      (t : F.obj T), P (F.map a t) (F.map b t)) : ∀ x y, P x y := by
  intro x y
  have hf := congrArg (fun f : F.obj X × F.obj Y ⟶ F.obj X ↦ f (x, y))
    (Functor.Monoidal.μ_fst F X Y)
  have hg := congrArg (fun f : F.obj X × F.obj Y ⟶ F.obj Y ↦ f (x, y))
    (Functor.Monoidal.μ_snd F X Y)
  change F.map (fst X Y) (μ F X Y (x, y)) = x at hf
  change F.map (snd X Y) (μ F X Y (x, y)) = y at hg
  simpa only [hf, hg] using h (X ⊗ Y) (fst _ _) (snd _ _) (μ F X Y (x, y))

omit [EssentiallySmall.{w} C] in
private theorem all₃ [F.Monoidal] {X Y Z : Sheaf J (Type w)}
    (P : F.obj X → F.obj Y → F.obj Z → Prop)
    (h : ∀ (T : Sheaf J (Type w)) (a : T ⟶ X) (b : T ⟶ Y) (c : T ⟶ Z)
      (t : F.obj T), P (F.map a t) (F.map b t) (F.map c t)) : ∀ x y z, P x y z := by
  apply all₂ F
  intro T a b t z
  let pair := μ F T Z (t, z)
  have hf := congrArg (fun f : F.obj T × F.obj Z ⟶ F.obj T ↦ f (t, z))
    (Functor.Monoidal.μ_fst F T Z)
  have hg := congrArg (fun f : F.obj T × F.obj Z ⟶ F.obj Z ↦ f (t, z))
    (Functor.Monoidal.μ_snd F T Z)
  change F.map (fst T Z) pair = t at hf
  change F.map (snd T Z) pair = z at hg
  have ha : F.map (fst T Z ≫ a) pair = F.map a t := by
    rw [F.map_comp]
    exact congrArg (F.map a) hf
  have hb : F.map (fst T Z ≫ b) pair = F.map b t := by
    rw [F.map_comp]
    exact congrArg (F.map b) hf
  simpa only [ha, hb, hg] using h (T ⊗ Z) (fst _ _ ≫ a) (fst _ _ ≫ b) (snd _ _) pair

variable {F}

omit [EssentiallySmall.{w} C] in
private theorem all₁ {X : Sheaf J (Type w)} (P : F.obj X → Prop)
    (h : ∀ (T : Sheaf J (Type w)) (a : T ⟶ X) (t : F.obj T), P (F.map a t)) :
    ∀ x, P x := by
  intro x
  simpa only [F.map_id, ConcreteCategory.id_apply] using h X (𝟙 X) x

private def rZero (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) : T ⟶ rset R :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       exact (R.obj.map f).hom.map_zero.symm }⟩

private def rNeg (R : Sheaf J CommRingCat.{w})
    {T : Sheaf J (Type w)} (a : T ⟶ rset R) : T ⟶ rset R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ -(@id (R.obj.obj U) (a.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       exact (congrArg (fun x : R.obj.obj V ↦ -x) ha).trans
         ((R.obj.map f).hom.map_neg _).symm }⟩

private def rAdd (R : Sheaf J CommRingCat.{w})
    {T : Sheaf J (Type w)} (a b : T ⟶ rset R) : T ⟶ rset R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ (@id (R.obj.obj U) (a.hom.app U x)) +
        (@id (R.obj.obj U) (b.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       have hb : b.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (b.hom.app U x) :=
         ConcreteCategory.congr_hom (b.hom.naturality f) x
       exact (congrArg₂ (fun x y : R.obj.obj V ↦ x + y) ha hb).trans
         ((R.obj.map f).hom.map_add _ _).symm }⟩

private def rOne (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) : T ⟶ rset R :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       exact (R.obj.map f).hom.map_one.symm }⟩

private def rMul (R : Sheaf J CommRingCat.{w})
    {T : Sheaf J (Type w)} (a b : T ⟶ rset R) : T ⟶ rset R :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ (@id (R.obj.obj U) (a.hom.app U x)) *
        (@id (R.obj.obj U) (b.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       have hb : b.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (b.hom.app U x) :=
         ConcreteCategory.congr_hom (b.hom.naturality f) x
       exact (congrArg₂ (fun x y : R.obj.obj V ↦ x * y) ha hb).trans
         ((R.obj.map f).hom.map_mul _ _).symm }⟩

private def mZero (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    (T : Sheaf J (Type w)) : T ⟶ (mset R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : M.val.obj U))
     naturality := by
       intro U V f
       ext x
       exact (M.val.map f).hom.map_zero.symm }⟩

private def mNeg (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    {T : Sheaf J (Type w)} (a : T ⟶ (mset R).obj M) : T ⟶ (mset R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ -(@id (M.val.obj U) (a.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (M.val.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       exact (congrArg (fun x : M.val.obj V ↦ -x) ha).trans
         ((M.val.map f).hom.map_neg _).symm }⟩

private def mAdd (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    {T : Sheaf J (Type w)} (a b : T ⟶ (mset R).obj M) : T ⟶ (mset R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ (@id (M.val.obj U) (a.hom.app U x)) +
        (@id (M.val.obj U) (b.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (M.val.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       have hb : b.hom.app V (T.obj.map f x) =
           (M.val.map f).hom (b.hom.app U x) :=
         ConcreteCategory.congr_hom (b.hom.naturality f) x
       exact (congrArg₂ (fun x y : M.val.obj V ↦ x + y) ha hb).trans
         ((M.val.map f).hom.map_add _ _).symm }⟩

private def mSMul (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    {T : Sheaf J (Type w)} (a : T ⟶ rset R) (b : T ⟶ (mset R).obj M) :
    T ⟶ (mset R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun x ↦
       (@id (R.obj.obj U) (a.hom.app U x)) • (@id (M.val.obj U) (b.hom.app U x)))
     naturality := by
       intro U V f
       ext x
       have ha : a.hom.app V (T.obj.map f x) =
           (R.obj.map f).hom (a.hom.app U x) :=
         ConcreteCategory.congr_hom (a.hom.naturality f) x
       have hb : b.hom.app V (T.obj.map f x) =
           (M.val.map f).hom (b.hom.app U x) :=
         ConcreteCategory.congr_hom (b.hom.naturality f) x
       exact (congrArg₂ (fun (r : R.obj.obj V) (m : M.val.obj V) ↦ r • m) ha hb).trans
         (M.val.map_smul f _ _).symm }⟩

private noncomputable def rzero (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) : F.obj (rset R) :=
  F.map (rZero R (𝟙_ _)) (ε F PUnit.unit)

private theorem eval_rzero
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) (x : F.obj T) :
    F.map (rZero R T) x =
      rzero F R := by
  exact eval_constant F _ _ (by ext U t; rfl) x

private noncomputable def rneg (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (x : F.obj (rset R)) : F.obj (rset R) :=
  F.map (rNeg R (𝟙 _)) x

private theorem eval_rneg
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) (a : T ⟶ rset R) (x : F.obj T) :
    F.map (rNeg R a) x =
      rneg F R (F.map a x) := by
  exact eval_unary F _ _ _ (by ext U t; rfl) x

private noncomputable def radd (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (x y : F.obj (rset R)) : F.obj (rset R) :=
  F.map (rAdd R (fst _ _) (snd _ _)) (μ F _ _ (x, y))

private theorem eval_radd
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) (a b : T ⟶ rset R) (x : F.obj T) :
    F.map (rAdd R a b) x =
      radd F R (F.map a x) (F.map b x) := by
  exact eval_binary F _ _ _ _ (by ext U t; rfl) x

private noncomputable def rone (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) : F.obj (rset R) :=
  F.map (rOne R (𝟙_ _)) (ε F PUnit.unit)

private theorem eval_rone
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) (x : F.obj T) :
    F.map (rOne R T) x =
      rone F R := by
  exact eval_constant F _ _ (by ext U t; rfl) x

private noncomputable def rmul (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (x y : F.obj (rset R)) : F.obj (rset R) :=
  F.map (rMul R (fst _ _) (snd _ _)) (μ F _ _ (x, y))

private theorem eval_rmul
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w)) (a b : T ⟶ rset R) (x : F.obj T) :
    F.map (rMul R a b) x =
      rmul F R (F.map a x) (F.map b x) := by
  exact eval_binary F _ _ _ _ (by ext U t; rfl) x

private noncomputable def mzero (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R)) : F.obj ((mset R).obj M) :=
  F.map (mZero R M (𝟙_ _)) (ε F PUnit.unit)

private theorem eval_mzero
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R))
    (T : Sheaf J (Type w)) (x : F.obj T) :
    F.map (mZero R M T) x =
      mzero F R M := by
  exact eval_constant F _ _ (by ext U t; rfl) x

private noncomputable def mneg (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R)) (x : F.obj ((mset R).obj M)) : F.obj ((mset R).obj M) :=
  F.map (mNeg R M (𝟙 _)) x

private theorem eval_mneg
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R))
    (T : Sheaf J (Type w)) (a : T ⟶ (mset R).obj M) (x : F.obj T) :
    F.map (mNeg R M a) x =
      mneg F R M (F.map a x) := by
  exact eval_unary F _ _ _ (by ext U t; rfl) x

private noncomputable def madd (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R)) (x y : F.obj ((mset R).obj M)) : F.obj ((mset R).obj M) :=
  F.map (mAdd R M (fst _ _) (snd _ _)) (μ F _ _ (x, y))

private theorem eval_madd
    (F : Sheaf J (Type w) ⥤ Type w) [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R))
    (T : Sheaf J (Type w)) (a b : T ⟶ (mset R).obj M) (x : F.obj T) :
    F.map (mAdd R M a b) x =
      madd F R M (F.map a x) (F.map b x) := by
  exact eval_binary F _ _ _ _ (by ext U t; rfl) x

-- Transport each algebraic identity by applying the evaluation lemmas to both sides.
private noncomputable abbrev rStructure (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) : CommRing (F.obj (rset R)) where
  zero := rzero F R
  add := radd F R
  neg := rneg F R
  nsmul := @nsmulRec _ ⟨rzero F R⟩ ⟨radd F R⟩
  zsmul := @zsmulRec _ ⟨rzero F R⟩ ⟨radd F R⟩ ⟨rneg F R⟩
    (@nsmulRec _ ⟨rzero F R⟩ ⟨radd F R⟩)
  one := rone F R
  mul := rmul F R
  add_assoc := by
    apply all₃ F
    intro T a b c t
    change radd F R (radd F R (F.map a t) (F.map b t)) (F.map c t) =
      radd F R (F.map a t) (radd F R (F.map b t) (F.map c t))
    have h : rAdd R (rAdd R a b) c =
        rAdd R a (rAdd R b c) := by
      ext U x
      exact add_assoc
        (@id (R.obj.obj U) (a.hom.app U x))
        (@id (R.obj.obj U) (b.hom.app U x))
        (@id (R.obj.obj U) (c.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  zero_add := by
    apply all₁ (F := F)
    intro T a t
    change radd F R (rzero F R) (F.map a t) =
      F.map a t
    have h : rAdd R (rZero R T) a =
        a := by
      ext U x
      exact zero_add (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  add_zero := by
    apply all₁ (F := F)
    intro T a t
    change radd F R (F.map a t) (rzero F R) =
      F.map a t
    have h : rAdd R a (rZero R T) =
        a := by
      ext U x
      exact add_zero (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  neg_add_cancel := by
    apply all₁ (F := F)
    intro T a t
    change radd F R (rneg F R (F.map a t)) (F.map a t) =
      rzero F R
    have h : rAdd R (rNeg R a) a =
        rZero R T := by
      ext U x
      exact neg_add_cancel (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  add_comm := by
    apply all₂ F
    intro T a b t
    change radd F R (F.map a t) (F.map b t) =
      radd F R (F.map b t) (F.map a t)
    have h : rAdd R a b =
        rAdd R b a := by
      ext U x
      exact add_comm (@id (R.obj.obj U) (a.hom.app U x)) (@id (R.obj.obj U) (b.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  mul_assoc := by
    apply all₃ F
    intro T a b c t
    change rmul F R (rmul F R (F.map a t) (F.map b t)) (F.map c t) =
      rmul F R (F.map a t) (rmul F R (F.map b t) (F.map c t))
    have h : rMul R (rMul R a b) c =
        rMul R a (rMul R b c) := by
      ext U x
      exact mul_assoc
        (@id (R.obj.obj U) (a.hom.app U x))
        (@id (R.obj.obj U) (b.hom.app U x))
        (@id (R.obj.obj U) (c.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  one_mul := by
    apply all₁ (F := F)
    intro T a t
    change rmul F R (rone F R) (F.map a t) =
      F.map a t
    have h : rMul R (rOne R T) a =
        a := by
      ext U x
      exact one_mul (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  mul_one := by
    apply all₁ (F := F)
    intro T a t
    change rmul F R (F.map a t) (rone F R) =
      F.map a t
    have h : rMul R a (rOne R T) =
        a := by
      ext U x
      exact mul_one (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  mul_comm := by
    apply all₂ F
    intro T a b t
    change rmul F R (F.map a t) (F.map b t) =
      rmul F R (F.map b t) (F.map a t)
    have h : rMul R a b =
        rMul R b a := by
      ext U x
      exact mul_comm (@id (R.obj.obj U) (a.hom.app U x)) (@id (R.obj.obj U) (b.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  left_distrib := by
    apply all₃ F
    intro T a b c t
    change rmul F R (F.map a t) (radd F R (F.map b t) (F.map c t)) =
      radd F R (rmul F R (F.map a t) (F.map b t)) (rmul F R (F.map a t) (F.map c t))
    have h : rMul R a (rAdd R b c) =
        rAdd R (rMul R a b) (rMul R a c) := by
      ext U x
      exact mul_add
        (@id (R.obj.obj U) (a.hom.app U x))
        (@id (R.obj.obj U) (b.hom.app U x))
        (@id (R.obj.obj U) (c.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  right_distrib := by
    apply all₃ F
    intro T a b c t
    change rmul F R (radd F R (F.map a t) (F.map b t)) (F.map c t) =
      radd F R (rmul F R (F.map a t) (F.map c t)) (rmul F R (F.map b t) (F.map c t))
    have h : rMul R (rAdd R a b) c =
        rAdd R (rMul R a c) (rMul R b c) := by
      ext U x
      exact add_mul
        (@id (R.obj.obj U) (a.hom.app U x))
        (@id (R.obj.obj U) (b.hom.app U x))
        (@id (R.obj.obj U) (c.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  mul_zero := by
    apply all₁ (F := F)
    intro T a t
    change rmul F R (F.map a t) (rzero F R) =
      rzero F R
    have h : rMul R a (rZero R T) =
        rZero R T := by
      ext U x
      exact mul_zero (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h
  zero_mul := by
    apply all₁ (F := F)
    intro T a t
    change rmul F R (rzero F R) (F.map a t) =
      rzero F R
    have h : rMul R (rZero R T) a =
        rZero R T := by
      ext U x
      exact zero_mul (@id (R.obj.obj U) (a.hom.app U x))
    simpa only [eval_radd, eval_rzero, eval_rneg, eval_rmul, eval_rone] using
      congrArg (fun f ↦ F.map f t) h

private noncomputable abbrev mStructure (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (base R)) : AddCommGroup (F.obj ((mset R).obj M)) where
  zero := mzero F R M
  add := madd F R M
  neg := mneg F R M
  nsmul := @nsmulRec _ ⟨mzero F R M⟩ ⟨madd F R M⟩
  zsmul := @zsmulRec _ ⟨mzero F R M⟩ ⟨madd F R M⟩ ⟨mneg F R M⟩
    (@nsmulRec _ ⟨mzero F R M⟩ ⟨madd F R M⟩)
  add_assoc := by
    apply all₃ F
    intro T a b c t
    change madd F R M (madd F R M (F.map a t) (F.map b t)) (F.map c t) =
      madd F R M (F.map a t) (madd F R M (F.map b t) (F.map c t))
    have h : mAdd R M (mAdd R M a b) c =
        mAdd R M a (mAdd R M b c) := by
      ext U x
      exact add_assoc
        (@id (M.val.obj U) (a.hom.app U x))
        (@id (M.val.obj U) (b.hom.app U x))
        (@id (M.val.obj U) (c.hom.app U x))
    simpa only [eval_madd, eval_mzero, eval_mneg] using
      congrArg (fun f ↦ F.map f t) h
  zero_add := by
    apply all₁ (F := F)
    intro T a t
    change madd F R M (mzero F R M) (F.map a t) =
      F.map a t
    have h : mAdd R M (mZero R M T) a =
        a := by
      ext U x
      exact zero_add (@id (M.val.obj U) (a.hom.app U x))
    simpa only [eval_madd, eval_mzero, eval_mneg] using
      congrArg (fun f ↦ F.map f t) h
  add_zero := by
    apply all₁ (F := F)
    intro T a t
    change madd F R M (F.map a t) (mzero F R M) =
      F.map a t
    have h : mAdd R M a (mZero R M T) =
        a := by
      ext U x
      exact add_zero (@id (M.val.obj U) (a.hom.app U x))
    simpa only [eval_madd, eval_mzero, eval_mneg] using
      congrArg (fun f ↦ F.map f t) h
  neg_add_cancel := by
    apply all₁ (F := F)
    intro T a t
    change madd F R M (mneg F R M (F.map a t)) (F.map a t) =
      mzero F R M
    have h : mAdd R M (mNeg R M a) a =
        mZero R M T := by
      ext U x
      exact neg_add_cancel (@id (M.val.obj U) (a.hom.app U x))
    simpa only [eval_madd, eval_mzero, eval_mneg] using
      congrArg (fun f ↦ F.map f t) h
  add_comm := by
    apply all₂ F
    intro T a b t
    change madd F R M (F.map a t) (F.map b t) =
      madd F R M (F.map b t) (F.map a t)
    have h : mAdd R M a b =
        mAdd R M b a := by
      ext U x
      exact add_comm (@id (M.val.obj U) (a.hom.app U x)) (@id (M.val.obj U) (b.hom.app U x))
    simpa only [eval_madd, eval_mzero, eval_mneg] using
      congrArg (fun f ↦ F.map f t) h

private noncomputable def msmul (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    (r : F.obj (rset R)) (x : F.obj ((mset R).obj M)) : F.obj ((mset R).obj M) :=
  F.map (mSMul R M (fst _ _) (snd _ _)) (μ F _ _ (r, x))

private theorem eval_msmul (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R))
    (T : Sheaf J (Type w)) (a : T ⟶ rset R) (b : T ⟶ (mset R).obj M)
    (x : F.obj T) :
    F.map (mSMul R M a b) x = msmul F R M (F.map a x) (F.map b x) := by
  exact eval_binary F _ _ _ _ (by ext U t; rfl) x

private noncomputable abbrev moduleStructure (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :
    letI := rStructure F R
    letI := mStructure F R M
    Module (F.obj (rset R)) (F.obj ((mset R).obj M)) := by
  letI := rStructure F R
  letI := mStructure F R M
  exact {
    smul := msmul F R M
    one_smul := by
      apply all₁ (F := F)
      intro T a t
      change msmul F R M (rone F R) (F.map a t) =
        F.map a t
      have h : mSMul R M (rOne R T) a =
          a := by
        ext U x
        change (1 : R.obj.obj U) • (@_root_.id (M.val.obj U) (a.hom.app U x)) = _
        exact one_smul (R.obj.obj U) _
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
    mul_smul := by
      apply all₃ F
      intro T a b c t
      change msmul F R M (rmul F R (F.map a t) (F.map b t)) (F.map c t) =
        msmul F R M (F.map a t) (msmul F R M (F.map b t) (F.map c t))
      have h : mSMul R M (rMul R a b) c =
          mSMul R M a (mSMul R M b c) := by
        ext U x
        exact mul_smul
          (@id (R.obj.obj U) (a.hom.app U x))
          (@id (R.obj.obj U) (b.hom.app U x))
          (@id (M.val.obj U) (c.hom.app U x))
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
    smul_add := by
      apply all₃ F
      intro T a b c t
      change msmul F R M (F.map a t) (madd F R M (F.map b t) (F.map c t)) =
        madd F R M (msmul F R M (F.map a t) (F.map b t)) (msmul F R M (F.map a t) (F.map c t))
      have h : mSMul R M a (mAdd R M b c) =
          mAdd R M (mSMul R M a b) (mSMul R M a c) := by
        ext U x
        exact smul_add
          (@id (R.obj.obj U) (a.hom.app U x))
          (@id (M.val.obj U) (b.hom.app U x))
          (@id (M.val.obj U) (c.hom.app U x))
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
    add_smul := by
      apply all₃ F
      intro T a b c t
      change msmul F R M (radd F R (F.map a t) (F.map b t)) (F.map c t) =
        madd F R M (msmul F R M (F.map a t) (F.map c t)) (msmul F R M (F.map b t) (F.map c t))
      have h : mSMul R M (rAdd R a b) c =
          mAdd R M (mSMul R M a c) (mSMul R M b c) := by
        ext U x
        exact add_smul
          (@id (R.obj.obj U) (a.hom.app U x))
          (@id (R.obj.obj U) (b.hom.app U x))
          (@id (M.val.obj U) (c.hom.app U x))
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
    smul_zero := by
      apply all₁ (F := F)
      intro T a t
      change msmul F R M (F.map a t) (mzero F R M) =
        mzero F R M
      have h : mSMul R M a (mZero R M T) =
          mZero R M T := by
        ext U x
        change (@_root_.id (R.obj.obj U) (a.hom.app U x)) • (0 : M.val.obj U) = _
        exact smul_zero _
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
    zero_smul := by
      apply all₁ (F := F)
      intro T a t
      change msmul F R M (rzero F R) (F.map a t) =
        mzero F R M
      have h : mSMul R M (rZero R T) a =
          mZero R M T := by
        ext U x
        change (0 : R.obj.obj U) • (@_root_.id (M.val.obj U) (a.hom.app U x)) = _
        exact zero_smul (R.obj.obj U) _
      simpa only [eval_msmul, eval_madd, eval_mzero, eval_radd, eval_rmul,
        eval_rone, eval_rzero] using congrArg (fun f ↦ F.map f t) h
  }

private noncomputable def imageRing (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) : CommRingCat.{w} := by
  letI := rStructure F R
  exact CommRingCat.of (F.obj (rset R))

private noncomputable def imageModule (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :
    ModuleCat.{w} (imageRing F R) := by
  letI := mStructure F R M
  letI : Module (imageRing F R) (F.obj ((mset R).obj M)) := moduleStructure F R M
  exact ModuleCat.of (imageRing F R) (F.obj ((mset R).obj M))

-- The underlying inverse-image map is linear because the original map is sectionwise linear.
private noncomputable def imageMap (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w})
    {M N : SheafOfModules.{w} (base R)} (f : M ⟶ N) :
    imageModule F R M ⟶ imageModule F R N :=
  ModuleCat.ofHom (X := imageModule F R M) (Y := imageModule F R N) {
    toFun := F.map ((mset R).map f)
    map_add' := by
      apply all₂ F
      intro T a b t
      change F.map ((mset R).map f) (madd F R M (F.map a t) (F.map b t)) =
        madd F R N (F.map ((mset R).map f) (F.map a t))
          (F.map ((mset R).map f) (F.map b t))
      have h : mAdd R M a b ≫ (mset R).map f =
          mAdd R N (a ≫ (mset R).map f) (b ≫ (mset R).map f) := by
        ext U x
        exact (f.val.app U).hom.map_add _ _
      have ht := congrArg (fun k ↦ F.map k t) h
      simpa only [F.map_comp, ConcreteCategory.comp_apply, eval_madd] using ht
    map_smul' := by
      apply all₂ F
      intro T a b t
      change F.map ((mset R).map f) (msmul F R M (F.map a t) (F.map b t)) =
        msmul F R N (F.map a t) (F.map ((mset R).map f) (F.map b t))
      have h : mSMul R M a b ≫ (mset R).map f =
          mSMul R N a (b ≫ (mset R).map f) := by
        ext U x
        exact (f.val.app U).hom.map_smul' _ _
      have ht := congrArg (fun k ↦ F.map k t) h
      simpa only [F.map_comp, ConcreteCategory.comp_apply, eval_msmul] using ht }

private noncomputable def imageFunctor (F : Sheaf J (Type w) ⥤ Type w)
    [F.Monoidal] (R : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{w} (base R) ⥤ ModuleCat.{w} (imageRing F R) where
  obj := imageModule F R
  map := imageMap F R
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change F.map ((mset R).map (𝟙 M)) x = x
    rw [(mset R).map_id, F.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change F.map ((mset R).map (f ≫ g)) x =
      F.map ((mset R).map g) (F.map ((mset R).map f) x)
    rw [(mset R).map_comp, F.map_comp]
    rfl

end PointTransport

open PointTransport

/-- The finite-product transport has a normalized presentation at every point.
Source: Stacks 00YV, 03D2 (auxiliary; not a blueprint node).

Proof: use the inverse binary-product and terminal comparisons of p.inverse to
transport the ring operations, and the addition and scalar action of every module.
Apply p.inverse to each algebraic identity and cancel its finite-product comparison;
this proves the ring and module axioms. Naturality makes the inverse image of a
module map linear and gives the natural underlying-set isomorphism. Addition of
module maps is addition followed by the diagonal pairing, so its transport also
proves additivity. The same calculation for arbitrary generalized sections gives
all the displayed operation-graph equations. No choice of unrelated ring or module
structures is involved: their operations are prescribed by these formulas. -/
theorem RingedSitePoint.nonempty
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (p : GeometricMorphism (Type w) (Sheaf J (Type w))) :
    Nonempty (RingedSitePoint R p) := by
  classical
  let : PreservesFiniteLimits p.inverse := p.leftExact
  let : p.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts p.inverse
  refine ⟨{
    ring := imageRing p.inverse R
    ringUnderlying := Iso.refl _
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    modules := imageFunctor p.inverse R
    moduleUnderlying := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
    modules_additive := ?_ }⟩
  · intro T a b t h x
    change p.inverse.map t x = radd p.inverse R (p.inverse.map a x) (p.inverse.map b x)
    rw [← eval_radd]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro T a b t h x
    change p.inverse.map t x = rmul p.inverse R (p.inverse.map a x) (p.inverse.map b x)
    rw [← eval_rmul]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro T a h x
    change p.inverse.map a x = rzero p.inverse R
    rw [← eval_rzero p.inverse R T x]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro T a h x
    change p.inverse.map a x = rone p.inverse R
    rw [← eval_rone p.inverse R T x]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro M T a b t h x
    change p.inverse.map t x = madd p.inverse R M (p.inverse.map a x) (p.inverse.map b x)
    rw [← eval_madd]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro M T a h x
    change p.inverse.map a x = mzero p.inverse R M
    rw [← eval_mzero p.inverse R M T x]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · intro M T a b t h x
    change p.inverse.map t x = msmul p.inverse R M (p.inverse.map a x) (p.inverse.map b x)
    rw [← eval_msmul]
    apply congrArg (fun f ↦ p.inverse.map f x)
    ext U z
    exact h U z
  · constructor
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change p.inverse.map ((mset R).map (f + g)) x =
      madd p.inverse R N (p.inverse.map ((mset R).map f) x)
        (p.inverse.map ((mset R).map g) x)
    have h : (mset R).map (f + g) = mAdd R N ((mset R).map f) ((mset R).map g) := by
      ext U z
      rfl
    rw [h, eval_madd]

end CategoryTheory
