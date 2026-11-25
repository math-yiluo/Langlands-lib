/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

public import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Constructing module functors through a geometric morphism

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace GeometricConstruction

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]

private noncomputable abbrev base (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev rset (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R

private noncomputable abbrev mset (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (base R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable def additiveObject (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) : CommGrp (Sheaf J (Type u)) := by
  let X := (mset R).obj M
  letI : GrpObj X := {
    one := ⟨{ app := fun W ↦ ↾(fun _ ↦ (show X.obj.obj W from (0 : M.val.obj W)))
              naturality := by intro U W f; ext x; exact (M.val.map f).hom.map_zero.symm }⟩
    mul := ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (M.val.obj W) inferInstance x.1 x.2)
              naturality := by intro U W f; ext x; exact ((M.val.map f).hom.map_add _ _).symm }⟩
    one_mul := by ext W x; exact @zero_add (M.val.obj W) inferInstance x.2
    mul_one := by ext W x; exact @add_zero (M.val.obj W) inferInstance x.1
    mul_assoc := by ext W x; exact @add_assoc (M.val.obj W) inferInstance x.1.1 x.1.2 x.2
    inv := ⟨{ app := fun W ↦ ↾(fun x ↦ @Neg.neg (M.val.obj W) inferInstance x)
              naturality := by intro U W f; ext x; exact ((M.val.map f).hom.map_neg _).symm }⟩
    left_inv := by ext W x; exact @neg_add_cancel (M.val.obj W) inferInstance x
    right_inv := by ext W x; exact @add_neg_cancel (M.val.obj W) inferInstance x }
  exact { X := X
          comm := { mul_comm := by ext W x; exact @add_comm (M.val.obj W) inferInstance x.2 x.1 } }

private abbrev sectionGroup (G : CommGrp (Sheaf K (Type u))) (W : Dᵒᵖ) :
    AddCommGroup (G.X.obj.obj W) where
  add a b := (MonObj.mul (X := G.X)).hom.app W (a, b)
  zero := (MonObj.one (X := G.X)).hom.app W PUnit.unit
  neg a := (GrpObj.inv (X := G.X)).hom.app W a
  add_assoc a b c := congrArg (fun f ↦ f.hom.app W ((a, b), c)) (MonObj.mul_assoc G.X)
  zero_add a := congrArg (fun f ↦ f.hom.app W (PUnit.unit, a)) (MonObj.one_mul G.X)
  add_zero a := congrArg (fun f ↦ f.hom.app W (a, PUnit.unit)) (MonObj.mul_one G.X)
  neg_add_cancel a := congrArg (fun f ↦ f.hom.app W a) (GrpObj.left_inv G.X)
  add_comm a b := congrArg (fun f ↦ f.hom.app W (b, a)) (IsCommMonObj.mul_comm G.X)
  nsmul := @nsmulRec _ ⟨(MonObj.one (X := G.X)).hom.app W PUnit.unit⟩
    ⟨fun a b ↦ (MonObj.mul (X := G.X)).hom.app W (a, b)⟩
  zsmul := @zsmulRec _ ⟨(MonObj.one (X := G.X)).hom.app W PUnit.unit⟩
    ⟨fun a b ↦ (MonObj.mul (X := G.X)).hom.app W (a, b)⟩
    ⟨fun a ↦ (GrpObj.inv (X := G.X)).hom.app W a⟩
    (@nsmulRec _ ⟨(MonObj.one (X := G.X)).hom.app W PUnit.unit⟩
      ⟨fun a b ↦ (MonObj.mul (X := G.X)).hom.app W (a, b)⟩)

private noncomputable def action (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) : rset R ⊗ (mset R).obj M ⟶ (mset R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance x.1 x.2)
     naturality := by
       intro U W f
       ext x
       exact (M.val.map_smul f x.1 x.2).symm }⟩

private noncomputable def addition (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) : (mset R).obj M ⊗ (mset R).obj M ⟶
      (mset R).obj M :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (M.val.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((M.val.map f).hom.map_add _ _).symm }⟩

private noncomputable def ringAdd (R : Sheaf J CommRingCat.{u}) :
    rset R ⊗ rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (R.obj.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((R.obj.map f).hom.map_add _ _).symm }⟩

private noncomputable def ringMul (R : Sheaf J CommRingCat.{u}) :
    rset R ⊗ rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Mul.mul (R.obj.obj W) inferInstance x.1 x.2)
     naturality := by intro U W f; ext x; exact ((R.obj.map f).hom.map_mul _ _).symm }⟩

private noncomputable def ringOne (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
     naturality := by intro U W f; ext x; exact (R.obj.map f).hom.map_one.symm }⟩

private noncomputable abbrev ringMonoid (R : Sheaf J CommRingCat.{u}) :
    MonObj (rset R) where
  one := ringOne R
  mul := ringMul R
  one_mul := by ext W x; exact @one_mul (R.obj.obj W) inferInstance x.2
  mul_one := by ext W x; exact @mul_one (R.obj.obj W) inferInstance x.1
  mul_assoc := by ext W x; exact @mul_assoc (R.obj.obj W) inferInstance x.1.1 x.1.2 x.2

private noncomputable abbrev moduleAction (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (base R)) :
    letI := ringMonoid R
    ModObj (rset R) ((mset R).obj M) := by
  letI := ringMonoid R
  exact ModObj.mk' _ (action R M)
    (by ext W x; exact @one_smul (R.obj.obj W) (M.val.obj W) _ _ x.2)
    (by ext W x; exact @mul_smul (R.obj.obj W) (M.val.obj W) _ _ x.1.1 x.1.2 x.2)

private noncomputable abbrev imageGroup (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [F.Braided] (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  F.mapCommGrp.obj (additiveObject R M)

private noncomputable abbrev imageAction (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    [F.Monoidal] (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (M : SheafOfModules.{u} (base R)) :
    rset B ⊗ F.obj ((mset R).obj M) ⟶ F.obj ((mset R).obj M) :=
  (d ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ F _ _ ≫ F.map (action R M)

private theorem imageAction_mulLaws
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    (hd : letI := ringMonoid R
          let := ringMonoid B
          let := F.monObjObj (rset R)
          IsMonHom d)
    (M : SheafOfModules.{u} (base R)) (W : Dᵒᵖ) :
    (∀ x, (imageAction F R B d M).hom.app W
      (show (rset B).obj.obj W from (1 : B.obj.obj W), x) = x) ∧
    (∀ (r s : B.obj.obj W) x,
      (imageAction F R B d M).hom.app W (r * s, x) =
        (imageAction F R B d M).hom.app W
          (r, (imageAction F R B d M).hom.app W (s, x))) := by
  let := ringMonoid R
  let := ringMonoid B
  let := moduleAction R M
  let := F.monObjObj (rset R)
  let := F.modObjObj (A := rset R) ((mset R).obj M)
  let : IsMonHom d := hd
  let := Mod.scalarRestriction d (F.obj ((mset R).obj M))
  constructor
  · intro x
    exact congrArg (fun f ↦ f.hom.app W (PUnit.unit, x))
      (ModObj.one_smul_self (rset B) (F.obj ((mset R).obj M)))
  · intro r s x
    exact congrArg (fun f ↦ f.hom.app W ((r, s), x))
      (ModObj.mul_smul_self (rset B) (F.obj ((mset R).obj M)))

private theorem map_lift
    {A₀ B₀ : Type*} [Category A₀] [Category B₀]
    [CartesianMonoidalCategory A₀] [CartesianMonoidalCategory B₀]
    (F : A₀ ⥤ B₀) [F.Monoidal] {P Q T : A₀}
    (a : T ⟶ P) (b : T ⟶ Q) {Z : B₀} (c : Z ⟶ F.obj T) :
    c ≫ F.map (CartesianMonoidalCategory.lift a b) =
      CartesianMonoidalCategory.lift (c ≫ F.map a) (c ≫ F.map b) ≫
        Functor.LaxMonoidal.μ F P Q := by
  rw [← Functor.Monoidal.lift_μ]
  simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift]

private theorem imageAction_add_smul
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    (hd : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (ringAdd R))
    (M : SheafOfModules.{u} (base R)) :
    let X' := rset B
    let Y' := F.obj ((mset R).obj M)
    let p := CartesianMonoidalCategory.fst (X' ⊗ X') Y'
    let q := CartesianMonoidalCategory.snd (X' ⊗ X') Y'
    let a := p ≫ CartesianMonoidalCategory.fst X' X'
    let b := p ≫ CartesianMonoidalCategory.snd X' X'
    CartesianMonoidalCategory.lift (p ≫ ringAdd B) q ≫ imageAction F R B d M =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift a q ≫ imageAction F R B d M)
        (CartesianMonoidalCategory.lift b q ≫ imageAction F R B d M) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (addition R M) := by
  let X := rset R
  let Y := (mset R).obj M
  let X' := rset B
  let p := CartesianMonoidalCategory.fst (X' ⊗ X') (F.obj Y)
  let q := CartesianMonoidalCategory.snd (X' ⊗ X') (F.obj Y)
  let a := p ≫ CartesianMonoidalCategory.fst X' X'
  let b := p ≫ CartesianMonoidalCategory.snd X' X'
  let t := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (a ≫ d) (b ≫ d) ≫
      Functor.LaxMonoidal.μ F X X) q ≫ Functor.LaxMonoidal.μ F (X ⊗ X) Y
  have ht1 : t ≫ F.map (CartesianMonoidalCategory.fst (X ⊗ X) Y) =
      CartesianMonoidalCategory.lift (a ≫ d) (b ≫ d) ≫
        Functor.LaxMonoidal.μ F X X := by
    rw [show t ≫ F.map (CartesianMonoidalCategory.fst (X ⊗ X) Y) =
      _ ≫ (Functor.LaxMonoidal.μ F (X ⊗ X) Y ≫
        F.map (CartesianMonoidalCategory.fst (X ⊗ X) Y)) from Category.assoc _ _ _]
    rw [Functor.Monoidal.μ_fst]
    exact CartesianMonoidalCategory.lift_fst _ _
  have ht2 : t ≫ F.map (CartesianMonoidalCategory.snd (X ⊗ X) Y) = q := by
    dsimp only [t]
    rw [Category.assoc, Functor.Monoidal.μ_snd]
    exact CartesianMonoidalCategory.lift_snd _ _
  have hs : CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫ ringAdd R)
      (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ action R M =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫ CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ action R M)
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (X ⊗ X) Y ≫ CartesianMonoidalCategory.snd X X)
        (CartesianMonoidalCategory.snd (X ⊗ X) Y) ≫ action R M) ≫ addition R M := by
    ext U z
    exact @add_smul (R.obj.obj U) (M.val.obj U) _ _ _ z.1.1 z.1.2 z.2
  have hpair : CartesianMonoidalCategory.lift (a ≫ d) (b ≫ d) = p ≫ (d ⊗ₘ d) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [a, b, Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.tensorHom_snd]
  have hm {Z : Sheaf K (Type u)} (f : Z ⟶ X') (g : Z ⟶ (F.obj Y)) :
      CartesianMonoidalCategory.lift (f ≫ d) g ≫
        Functor.LaxMonoidal.μ F X Y ≫ F.map (action R M) =
          CartesianMonoidalCategory.lift f g ≫ imageAction F R B d M := by
    rw [show CartesianMonoidalCategory.lift (f ≫ d) g =
      CartesianMonoidalCategory.lift f g ≫ (d ⊗ₘ 𝟙 _) by
        apply CartesianMonoidalCategory.hom_ext <;>
          simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
            CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_snd,
            CartesianMonoidalCategory.tensorHom_fst,
            CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]]
    rfl
  have hh := congrArg (fun k ↦ t ≫ F.map k) hs
  simp only [Functor.map_comp, ← Category.assoc, map_lift, ht1, ht2] at hh
  simp only [Category.assoc, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd] at hh
  dsimp only [X, Y, X'] at hh
  simp only [hpair, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
    CartesianMonoidalCategory.tensorHom_snd, ← hd] at hh
  rw [← Category.assoc p (ringAdd B) d,
    ← Category.assoc p (CartesianMonoidalCategory.fst X' X') d,
    ← Category.assoc p (CartesianMonoidalCategory.snd X' X') d] at hh
  rw [hm, hm, hm] at hh
  exact hh

private theorem imageAction_smul_add
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (M : SheafOfModules.{u} (base R)) :
    let X' := rset B
    let Y' := F.obj ((mset R).obj M)
    let p := CartesianMonoidalCategory.fst X' (Y' ⊗ Y')
    let q := CartesianMonoidalCategory.snd X' (Y' ⊗ Y')
    let b := q ≫ CartesianMonoidalCategory.fst Y' Y'
    let c := q ≫ CartesianMonoidalCategory.snd Y' Y'
    CartesianMonoidalCategory.lift p
        (q ≫ Functor.LaxMonoidal.μ F _ _ ≫ F.map (addition R M)) ≫
        imageAction F R B d M =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift p b ≫ imageAction F R B d M)
        (CartesianMonoidalCategory.lift p c ≫ imageAction F R B d M) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (addition R M) := by
  let X := rset R
  let Y := (mset R).obj M
  let X' := rset B
  let p := CartesianMonoidalCategory.fst X' (F.obj Y ⊗ F.obj Y)
  let q := CartesianMonoidalCategory.snd X' (F.obj Y ⊗ F.obj Y)
  let b := q ≫ CartesianMonoidalCategory.fst (F.obj Y) (F.obj Y)
  let c := q ≫ CartesianMonoidalCategory.snd (F.obj Y) (F.obj Y)
  let t := CartesianMonoidalCategory.lift (p ≫ d)
    (q ≫ Functor.LaxMonoidal.μ F Y Y) ≫ Functor.LaxMonoidal.μ F X (Y ⊗ Y)
  have ht1 : t ≫ F.map (CartesianMonoidalCategory.fst X (Y ⊗ Y)) = p ≫ d := by
    simp only [t, Category.assoc, Functor.Monoidal.μ_fst,
      CartesianMonoidalCategory.lift_fst]
  have ht2 : t ≫ F.map (CartesianMonoidalCategory.snd X (Y ⊗ Y)) =
      q ≫ Functor.LaxMonoidal.μ F Y Y := by
    dsimp only [t]
    rw [Category.assoc, Functor.Monoidal.μ_snd]
    exact CartesianMonoidalCategory.lift_snd _ _
  have hs : CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst X (Y ⊗ Y))
      (CartesianMonoidalCategory.snd X (Y ⊗ Y) ≫ addition R M) ≫ action R M =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst X (Y ⊗ Y))
        (CartesianMonoidalCategory.snd X (Y ⊗ Y) ≫ CartesianMonoidalCategory.fst Y Y) ≫
          action R M)
      (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst X (Y ⊗ Y))
        (CartesianMonoidalCategory.snd X (Y ⊗ Y) ≫ CartesianMonoidalCategory.snd Y Y) ≫
          action R M) ≫ addition R M := by
    ext U z
    exact smul_add (show R.obj.obj U from z.1)
      (show M.val.obj U from z.2.1) (show M.val.obj U from z.2.2)
  have hm {Z : Sheaf K (Type u)} (f : Z ⟶ X') (g : Z ⟶ F.obj Y) :
      CartesianMonoidalCategory.lift (f ≫ d) g ≫
        Functor.LaxMonoidal.μ F X Y ≫ F.map (action R M) =
          CartesianMonoidalCategory.lift f g ≫ imageAction F R B d M := by
    rw [show CartesianMonoidalCategory.lift (f ≫ d) g =
      CartesianMonoidalCategory.lift f g ≫ (d ⊗ₘ 𝟙 _) by
        apply CartesianMonoidalCategory.hom_ext <;>
          simp only [Category.assoc, CartesianMonoidalCategory.lift_fst,
            CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_snd,
            CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd,
            Category.comp_id]]
    rfl
  have hh := congrArg (fun k ↦ t ≫ F.map k) hs
  simp only [Functor.map_comp, ← Category.assoc, map_lift, ht1, ht2] at hh
  simp only [Category.assoc, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd] at hh
  rw [hm, hm, hm] at hh
  exact hh

private noncomputable def imageModule
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    (ha : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (ringAdd R))
    (hm : letI := ringMonoid R
          letI := ringMonoid B
          letI := F.monObjObj (rset R)
          IsMonHom d)
    (M : SheafOfModules.{u} (base R)) : SheafOfModules.{u} (base B) := by
  let G := imageGroup F R M
  letI (W : Dᵒᵖ) : AddCommGroup ((F.obj ((mset R).obj M)).obj.obj W) := sectionGroup G W
  letI : GrpObj (F.obj ((mset R).obj M)) := G.grp
  let act := imageAction F R B d M
  letI (W : Dᵒᵖ) : Module (B.obj.obj W) ((F.obj ((mset R).obj M)).obj.obj W) := {
    smul := fun r x ↦ act.hom.app W (r, x)
    one_smul := (imageAction_mulLaws F R B d hm M W).1
    mul_smul := (imageAction_mulLaws F R B d hm M W).2
    smul_add := fun r x y ↦
      congrArg (fun f ↦ f.hom.app W (r, (x, y))) (imageAction_smul_add F R B d M)
    add_smul := fun r s x ↦
      congrArg (fun f ↦ f.hom.app W ((r, s), x)) (imageAction_add_smul F R B d ha M)
    smul_zero := by
      intro r
      have h := congrArg (fun f ↦ f.hom.app W (r, (0, 0)))
        (imageAction_smul_add F R B d M)
      change act.hom.app W (r, 0 + 0) =
        act.hom.app W (r, 0) + act.hom.app W (r, 0) at h
      have hz : (0 : (F.obj ((mset R).obj M)).obj.obj W) + 0 = 0 := add_zero _
      rw [hz] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    zero_smul := by
      intro x
      have h := congrArg (fun f ↦ f.hom.app W (((0 : B.obj.obj W), (0 : B.obj.obj W)), x))
        (imageAction_add_smul F R B d ha M)
      change act.hom.app W ((0 : B.obj.obj W) + 0, x) =
        act.hom.app W ((0 : B.obj.obj W), x) + act.hom.app W ((0 : B.obj.obj W), x) at h
      have hz : (0 : B.obj.obj W) + 0 = 0 := add_zero _
      rw [hz] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm) }
  let N : PresheafOfModules.{u} (base B).obj := {
    obj W := ModuleCat.of (B.obj.obj W) ((F.obj ((mset R).obj M)).obj.obj W)
    map {U W} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((base B).obj.map f).hom).obj
        (ModuleCat.of (B.obj.obj W) ((F.obj ((mset R).obj M)).obj.obj W))) {
      toFun := (F.obj ((mset R).obj M)).obj.map f
      map_add' := fun x y ↦
        (congrArg (fun g ↦ g (x, y))
          ((MonObj.mul (X := (F.obj ((mset R).obj M)))).hom.naturality f)).symm
      map_smul' := fun r x ↦
        (congrArg (fun g ↦ g (r, x)) (act.hom.naturality f)).symm }
    map_id W := by ext x; exact congrArg (fun g ↦ g x) ((F.obj ((mset R).obj M)).obj.map_id W)
    map_comp f g := by
      ext x
      exact congrArg (fun k ↦ k x) ((F.obj ((mset R).obj M)).obj.map_comp f g) }
  refine ⟨N, (Presheaf.isSheaf_of_isSheaf_comp K _
    (CategoryTheory.forget AddCommGrpCat.{u})) ?_⟩
  change Presheaf.IsSheaf K (F.obj ((mset R).obj M)).obj
  exact (F.obj ((mset R).obj M)).property

private noncomputable def additiveMap {R : Sheaf J CommRingCat.{u}}
    {M N : SheafOfModules.{u} (base R)} (f : M ⟶ N) :
    additiveObject R M ⟶ additiveObject R N :=
  InducedCategory.homMk (Grp.homMk'' ((mset R).map f)
    (by ext W x; exact (f.val.app W).hom.map_zero)
    (by ext W x; exact (f.val.app W).hom.map_add _ _))

private theorem imageAction_map
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    {M N : SheafOfModules.{u} (base R)} (f : M ⟶ N) :
    imageAction F R B d M ≫ F.map ((mset R).map f) =
      (𝟙 _ ⊗ₘ F.map ((mset R).map f)) ≫ imageAction F R B d N := by
  have hs : action R M ≫ (mset R).map f =
      (𝟙 _ ⊗ₘ (mset R).map f) ≫ action R N := by
    ext W x
    exact (f.val.app W).hom.map_smul' x.1 x.2
  simp only [imageAction, Category.assoc, ← F.map_comp, hs]
  rw [F.map_comp, id_tensorHom, ← Functor.LaxMonoidal.μ_natural_right_assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

private noncomputable def imageMap
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    (ha : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (ringAdd R))
    (hm : letI := ringMonoid R
          letI := ringMonoid B
          letI := F.monObjObj (rset R)
          IsMonHom d)
    {M N : SheafOfModules.{u} (base R)} (f : M ⟶ N) :
    imageModule F R B d ha hm M ⟶ imageModule F R B d ha hm N where
  val := {
    app W := ModuleCat.ofHom
      (X := (imageModule F R B d ha hm M).val.obj W)
      (Y := (imageModule F R B d ha hm N).val.obj W) {
      toFun := (F.map ((mset R).map f)).hom.app W
      map_add' := by
        intro x y
        let g := F.mapCommGrp.map (additiveMap f)
        exact congrArg (fun k ↦ k.hom.app W (x, y))
          (IsMonHom.mul_hom g.hom.hom.hom)
      map_smul' := fun r x ↦ congrArg (fun k ↦ k.hom.app W (r, x))
        (imageAction_map F R B d f) }
    naturality := by
      intro U W i
      ext x
      exact CategoryTheory.congr_fun ((F.map ((mset R).map f)).hom.naturality i) x }

private noncomputable def imageFunctor
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R))
    (ha : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (ringAdd R))
    (hm : letI := ringMonoid R
          letI := ringMonoid B
          letI := F.monObjObj (rset R)
          IsMonHom d) : SheafOfModules.{u} (base R) ⥤ SheafOfModules.{u} (base B) where
  obj := imageModule F R B d ha hm
  map := imageMap F R B d ha hm
  map_id M := by
    ext W x
    exact congrArg (fun k ↦ k.hom.app W x)
      (show F.map ((mset R).map (𝟙 M)) = 𝟙 _ by rw [(mset R).map_id, F.map_id])
  map_comp f g := by
    ext W x
    exact congrArg (fun k ↦ k.hom.app W x)
      (show F.map ((mset R).map (f ≫ g)) =
        F.map ((mset R).map f) ≫ F.map ((mset R).map g) by
          rw [Functor.map_comp, F.map_comp])

private noncomputable def imageFunctorUnderlying
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (ha hm) :
    imageFunctor F R B d ha hm ⋙ mset B ≅ mset R ⋙ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; rfl)

private noncomputable abbrev productExists
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    (X Y : Sheaf T (Type u)) : HasBinaryProduct X Y := inferInstance

attribute [local instance] productExists

private noncomputable def fromProd
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    (X Y : Sheaf T (Type u)) : X ⨯ Y ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift prod.fst prod.snd

@[reassoc] private theorem fromProd_fst
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    (X Y : Sheaf T (Type u)) :
    fromProd X Y ≫ CartesianMonoidalCategory.fst X Y = prod.fst :=
  CartesianMonoidalCategory.lift_fst _ _

@[reassoc] private theorem fromProd_snd
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    (X Y : Sheaf T (Type u)) :
    fromProd X Y ≫ CartesianMonoidalCategory.snd X Y = prod.snd :=
  CartesianMonoidalCategory.lift_snd _ _

@[reassoc] private theorem fromProd_map
    {E : Type uE} [Category.{vE} E]
    {T : GrothendieckTopology E}
    {X Y X' Y' : Sheaf T (Type u)} (f : X ⟶ X') (g : Y ⟶ Y') :
    prod.map f g ≫ fromProd X' Y' = fromProd X Y ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, fromProd_fst, fromProd_snd,
      CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.tensorHom_snd,
      fromProd_fst_assoc, fromProd_snd_assoc, prod.map_fst, prod.map_snd]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] in
private theorem fromProd_comparison
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X Y : Sheaf J (Type u)) :
    prodComparison F X Y ≫ fromProd (F.obj X) (F.obj Y) ≫
      Functor.LaxMonoidal.μ F X Y = F.map (fromProd X Y) := by
  apply (cancel_mono (CartesianMonoidalCategory.prodComparison F X Y)).1
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
      CartesianMonoidalCategory.prodComparison_snd, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd, fromProd_fst, fromProd_snd,
      prodComparison_fst, prodComparison_snd, ← F.map_comp]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] in
private theorem binary_transport_iff
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X : Sheaf J (Type u)) (A : Sheaf K (Type u)) (e : A ≅ F.obj X)
    (a : X ⊗ X ⟶ X) (b : A ⊗ A ⟶ A) :
    (F.map (fromProd X X ≫ a) = prodComparison F X X ≫
      prod.map e.inv e.inv ≫ fromProd A A ≫ b ≫ e.hom) ↔
    (b ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ Functor.LaxMonoidal.μ F X X ≫ F.map a) := by
  have hc := fromProd_comparison F X X
  have ht : IsIso (fromProd (F.obj X) (F.obj X)) := by
    let e' : F.obj X ⨯ F.obj X ≅ F.obj X ⊗ F.obj X :=
      (limit.isLimit (pair (F.obj X) (F.obj X))).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
    have he : e'.hom = fromProd _ _ := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (limit.isLimit (pair _ _)).conePointUniqueUpToIso_hom_comp _
          ⟨WalkingPair.left⟩
      · exact (limit.isLimit (pair _ _)).conePointUniqueUpToIso_hom_comp _
          ⟨WalkingPair.right⟩
    rw [← he]
    infer_instance
  simp only [F.map_comp, ← hc, Category.assoc, fromProd_map_assoc, cancel_epi]
  constructor
  · intro h
    have h' := congrArg (fun z ↦ (e.hom ⊗ₘ e.hom) ≫ z) h
    simpa only [← Category.assoc, tensorHom_comp_tensorHom,
      e.hom_inv_id, id_tensorHom_id, Category.id_comp] using h'.symm
  · intro h
    rw [h]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      e.inv_hom_id, id_tensorHom_id, Category.id_comp]

private theorem ringIso_isMonHom
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
    (e : rset A ≅ F.obj (rset R))
    (h : ringMul A ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (ringMul R)) :
    letI := ringMonoid R
    letI := ringMonoid A
    letI := F.monObjObj (rset R)
    IsMonHom e.hom := by
  let := ringMonoid R
  let := ringMonoid A
  let := F.monObjObj (rset R)
  let t := MonObj.ofIso e.symm
  have ht : t = ringMonoid A := by
    apply MonObj.ext
    apply (cancel_mono e.hom).1
    change ((e.hom ⊗ₘ e.hom) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (ringMul R) ≫ e.inv) ≫ e.hom = ringMul A ≫ e.hom
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h.symm
  have hOne := congrArg (fun z : MonObj (rset A) ↦
    letI := z; (MonObj.one : 𝟙_ _ ⟶ rset A)) ht
  let : MonObj (rset A) := ringMonoid A
  refine ⟨?_, h⟩
  change ringOne A ≫ e.hom = Functor.LaxMonoidal.ε F ≫ F.map (ringOne R)
  change Functor.LaxMonoidal.ε F ≫ F.map (ringOne R) ≫ e.inv = ringOne A at hOne
  rw [← hOne]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] in
private theorem adjunct_binary
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [L.Monoidal] [V.Monoidal]
    (X : Sheaf J (Type u)) (Y : Sheaf K (Type u))
    (a : X ⊗ X ⟶ X) (b : Y ⊗ Y ⟶ Y) (g : L.obj X ⟶ Y)
    (h : L.map a ≫ g = CartesianMonoidalCategory.prodComparison L X X ≫
      (g ⊗ₘ g) ≫ b) :
    a ≫ adj.homEquiv X Y g = (adj.homEquiv X Y g ⊗ₘ adj.homEquiv X Y g) ≫
      Functor.LaxMonoidal.μ V Y Y ≫ V.map b := by
  let d := adj.homEquiv X Y g
  have hp : adj.homEquiv (X ⊗ X) (Y ⊗ Y)
      (CartesianMonoidalCategory.prodComparison L X X ≫ (g ⊗ₘ g)) =
      (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V Y Y := by
    apply (cancel_mono (CartesianMonoidalCategory.prodComparison V Y Y)).1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst,
        Functor.Monoidal.μ_fst, CartesianMonoidalCategory.tensorHom_fst]
      rw [← adj.homEquiv_naturality_right]
      simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.prodComparison_fst_assoc]
      rw [adj.homEquiv_naturality_left]
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd,
        Functor.Monoidal.μ_snd, CartesianMonoidalCategory.tensorHom_snd]
      rw [← adj.homEquiv_naturality_right]
      simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.prodComparison_snd_assoc]
      rw [adj.homEquiv_naturality_left]
  rw [← adj.homEquiv_naturality_left, h, ← Category.assoc,
    adj.homEquiv_naturality_right, hp]
  rfl

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] in
private theorem adjunct_constant
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [L.Monoidal] [V.Monoidal]
    (X : Sheaf J (Type u)) (Y : Sheaf K (Type u))
    (a : 𝟙_ _ ⟶ X) (b : 𝟙_ _ ⟶ Y) (g : L.obj X ⟶ Y)
    (h : L.map a ≫ g = CartesianMonoidalCategory.terminalComparison L ≫ b) :
    a ≫ adj.homEquiv X Y g = Functor.LaxMonoidal.ε V ≫ V.map b := by
  have ht : adj.homEquiv (𝟙_ _) (𝟙_ _) (CartesianMonoidalCategory.terminalComparison L) =
      Functor.LaxMonoidal.ε V := by
    apply (cancel_mono (CartesianMonoidalCategory.terminalComparison V)).1
    exact CartesianMonoidalCategory.toUnit_unique _ _
  rw [← adj.homEquiv_naturality_left, h, adj.homEquiv_naturality_right, ht]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D] in
private theorem binary_inverse
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    (X : Sheaf J (Type u)) (A : Sheaf K (Type u)) (e : A ≅ F.obj X)
    (a : X ⊗ X ⟶ X) (b : A ⊗ A ⟶ A)
    (h : b ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ Functor.LaxMonoidal.μ F X X ≫ F.map a) :
    F.map a ≫ e.inv = CartesianMonoidalCategory.prodComparison F X X ≫
      (e.inv ⊗ₘ e.inv) ≫ b := by
  apply (cancel_epi ((e.hom ⊗ₘ e.hom) ≫ Functor.LaxMonoidal.μ F X X)).1
  simp only [Category.assoc, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
    Functor.Monoidal.μ_δ_assoc]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, e.hom_inv_id,
    id_tensorHom_id, Category.id_comp]
  simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using
    congrArg (fun z ↦ z ≫ e.inv) h.symm

private theorem ringMap_add (R S : Sheaf J CommRingCat.{u}) (c : R ⟶ S) :
    ringAdd R ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c ⊗ₘ
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) ≫ ringAdd S := by
  ext W x
  exact (c.hom.app W).hom.map_add x.1 x.2

private theorem ringMap_mul (R S : Sheaf J CommRingCat.{u}) (c : R ⟶ S) :
    ringMul R ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c ⊗ₘ
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) ≫ ringMul S := by
  ext W x
  exact (c.hom.app W).hom.map_mul x.1 x.2

private theorem ringMap_one (R S : Sheaf J CommRingCat.{u}) (c : R ⟶ S) :
    ringOne R ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c = ringOne S := by
  ext W x
  exact (c.hom.app W).hom.map_one

private theorem imageModule_addition
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (ha hm) (M : SheafOfModules.{u} (base R)) :
    addition B (imageModule F R B d ha hm M) =
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (addition R M) := rfl

private theorem imageModule_action
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (ha hm) (M : SheafOfModules.{u} (base R)) :
    action B (imageModule F R B d ha hm M) = imageAction F R B d M := rfl

private theorem imageModule_addition_comparison
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (ha hm) (M : SheafOfModules.{u} (base R)) :
    F.map (fromProd _ _ ≫ addition R M) = prodComparison F _ _ ≫
      fromProd _ _ ≫ addition B (imageModule F R B d ha hm M) := by
  rw [imageModule_addition, F.map_comp, ← fromProd_comparison]
  simp only [Category.assoc]

private theorem imageModule_action_comparison
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (e : rset B ≅ F.obj (rset R)) (ha hm) (M : SheafOfModules.{u} (base R)) :
    F.map (fromProd _ _ ≫ action R M) = prodComparison F _ _ ≫
      prod.map e.inv (𝟙 _) ≫ fromProd _ _ ≫
        action B (imageModule F R B e.hom ha hm M) := by
  rw [imageModule_action]
  dsimp only [imageAction]
  simp only [fromProd_map_assoc,
    tensorHom_comp_tensorHom_assoc, e.inv_hom_id, Category.id_comp,
    id_tensorHom_id]
  rw [F.map_comp, ← fromProd_comparison]
  simp only [Category.assoc]

private theorem imageModule_action_comparison_right
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Braided]
    (R : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (d : rset B ⟶ F.obj (rset R)) (ha hm) (M : SheafOfModules.{u} (base R)) :
    fromProd _ _ ≫ action B (imageModule F R B d ha hm M) =
      prod.map d (𝟙 _) ≫ inv (prodComparison F _ _) ≫
        F.map (fromProd _ _ ≫ action R M) := by
  rw [imageModule_action]
  dsimp only [imageAction]
  rw [F.map_comp, ← fromProd_comparison]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, fromProd_map_assoc]
  rfl

end GeometricConstruction

open GeometricConstruction

-- Keep the pre-existing named nondependent forall binder `hRing` unchanged.
set_option linter.unusedVariables false in
-- The statement records every operation and its underlying comparison.
/-- Construct the transported module functors and their operation comparisons.
Source: Stacks Project, Tags 03D1 and 03D2, `lemma-pushforward-module`
and `lemma-pullback-module`.
(auxiliary; not a blueprint node).

Proof: L preserves finite products, and V does so because it is a right adjoint.
For M, transport addition, zero, negation and scalar multiplication through L,
using the inverse terminal and binary-product comparisons and the ring
identification eR. Each module identity is an equality between composites of
these operations; functoriality and product preservation transport these
identities. More explicitly, give L the monoidal structure from its chosen
finite products. Addition, zero and negation are the image additive-group
object. The image module-object action satisfies multiplicative associativity
and the unit law. Transport the two distributivity diagrams by the invertible
comparisons for R times M times M and R times R times M; naturality carries
their projections and pairings to the target projections and pairings. The
resulting four equations are the minimal module axioms on sections.
The comparison eR preserves addition and multiplication by hRing. Transport
the multiplicative monoid along eR; its multiplication is the given one on A.
The uniqueness theorem for a monoid structure with fixed multiplication
(`MonObj.ext`) identifies its unit with A's unit. The same argument identifies
zero for the additive group, and inverse preservation follows by uniqueness.
Thus no missing unit hypothesis is used. Evaluating on each object gives an A-module,
and naturality makes restrictions linear. The set presheaf is the sheaf L(M),
so this defines I(M). Applying L to a linear map gives I on morphisms and eI.
Likewise, transport H through V, then restrict its scalar action along the
adjunct of eR.inv followed by c. This adjunct is a ring morphism: the unit
of a cartesian monoidal adjunction preserves the transported ring operations,
and composing it with V of the ring morphism eR.inv followed by c preserves
those operations. Equivalently, compute its binary-operation mates and its
terminal-operation mate. Evaluating gives P(H) with underlying sheaf
V(H); V on maps gives P and eP. The sectionwise operation formulas hold by
construction. The addition comparison is product preservation. The scalar
map k is the inverse product comparison for V applied to the pair of the
adjunct of c and eP.hom; composing with either projection yields its stated
projection equation, and composing with V of scalar multiplication gives
the final scalar-action equation. These constructions also apply to the
zero ring, zero modules and the empty site because they use only finite
product diagrams, with no choice of local nonzero elements. -/
theorem geometric_module_construction
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    :
    letI : ∀ X Y : Sheaf J (Type u), HasBinaryProduct X Y := fun _ _ ↦ inferInstance
    letI : ∀ X Y : Sheaf K (Type u), HasBinaryProduct X Y := fun _ _ ↦ inferInstance
    ∀ (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u}) (eR : ((sheafCompose K (CategoryTheory.forget
      CommRingCat.{u})).obj A) ≅ L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
      R))
      (addR mulR : (Limits.prod ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)) ⟶
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R))
      (addA mulA : (Limits.prod ((sheafCompose K
        (CategoryTheory.forget CommRingCat.{u})).obj A)
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)) ⟶
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A))
    (hRing : (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        addR.hom.app W x = @Add.add (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        mulR.hom.app W x = @Mul.mul (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        addA.hom.app W x = @Add.add (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        mulA.hom.app W x = @Mul.mul (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      L.map addR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ addA ≫ eR.hom ∧
      L.map mulR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ mulA ≫ eR.hom)
    (c : A ⟶ S),
      ∃ (I : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
        (P : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅ (toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})) ⋙ L)
        (eP : P ⋙ (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ≅ (toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})) ⋙ V),
        (∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ∃ (addM : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
            CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
            AddCommGrpCat.{u})).obj M))
            (muM : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj M))
            (addI : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M)))
            (muI : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M))),
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose
        J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
        AddCommGrpCat.{u})).obj M)).obj.obj W),
        addM.hom.app W x = @Add.add (M.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          M)).hom.app W x) : M.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).obj.obj W),
        muM.hom.app W x = @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        addI.hom.app W x = @Add.add ((I.obj M).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M))).hom.app W x) : (I.obj M).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) :
          (I.obj M).val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        muI.hom.app W x = @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) : A.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) : (I.obj M).val.obj W)) ∧
          L.map addM = prodComparison L ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
            ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose
            J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M ∧
          L.map muM = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
            R) ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M) ∧
        (∀ H : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
          ∃ (addH : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
            (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
            CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H))
            (muH : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))
            (addP : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
              sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (muP : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (k : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ V.obj (((sheafCompose K
              (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf ((sheafCompose K (forget₂
              CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))),
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose
        K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
        AddCommGrpCat.{u})).obj H)).obj.obj W),
        addH.hom.app W x = @Add.add (H.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          H)).hom.app W x) : H.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).obj.obj W),
        muH.hom.app W x = @SMul.smul (S.obj.obj W) (H.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj S)).hom.app W x) : S.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        addP.hom.app W x = @Add.add ((P.obj H).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H))).hom.app W x) : (P.obj H).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) :
          (P.obj H).val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        muP.hom.app W x = @SMul.smul (R.obj.obj W) ((P.obj H).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) : (P.obj H).val.obj W)) ∧
          V.map addH = prodComparison V ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ≫
            prod.map (eP.inv.app H) (eP.inv.app H) ≫ addP ≫ eP.hom.app H ∧
          k ≫ V.map (prod.fst : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
            (CategoryTheory.forget CommRingCat.{u})).obj S)) =
            (prod.fst : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
              (CategoryTheory.forget CommRingCat.{u})).obj R)) ≫
              adj.homEquiv ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
                ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S)
                (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
          k ≫ V.map (prod.snd : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
            (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H)) =
            (prod.snd : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H))) ≫ eP.hom.app H ∧
          muP ≫ eP.hom.app H = k ≫ V.map muH) := by
  dsimp only
  intro L V adj hL R S A eR addR mulR addA mulA hRing c
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : V.Braided := Functor.Braided.ofChosenFiniteProducts V
  obtain ⟨haddR, hmulR, haddA, hmulA, hadd, hmul⟩ := hRing
  have hAR : addR = fromProd _ _ ≫ ringAdd R := by
    ext W x
    exact haddR W x
  have hMR : mulR = fromProd _ _ ≫ ringMul R := by
    ext W x
    exact hmulR W x
  have hAA : addA = fromProd _ _ ≫ ringAdd A := by
    ext W x
    exact haddA W x
  have hMA : mulA = fromProd _ _ ≫ ringMul A := by
    ext W x
    exact hmulA W x
  rw [hAR, hAA] at hadd
  rw [hMR, hMA] at hmul
  have haI := (binary_transport_iff L _ _ eR (ringAdd R) (ringAdd A)).1 hadd
  have hmI := ringIso_isMonHom L R A eR
    ((binary_transport_iff L _ _ eR (ringMul R) (ringMul A)).1 hmul)
  let g := eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map c
  let d := adj.homEquiv (rset R) (rset S) g
  have haP : ringAdd R ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd S) := by
    apply adjunct_binary L V adj _ _ _ _ g
    dsimp only [g]
    rw [← Category.assoc, binary_inverse L _ _ eR _ _ haI]
    rw [Category.assoc, Category.assoc, ringMap_add]
    simp only [← Category.assoc, tensorHom_comp_tensorHom]
  have hmP : let := ringMonoid S
             let := ringMonoid R
             let := V.monObjObj (rset S)
             IsMonHom d := by
    let := ringMonoid R
    let := ringMonoid A
    let := ringMonoid S
    let := L.monObjObj (rset R)
    let : IsMonHom eR.hom := hmI
    let := V.monObjObj (rset S)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant L V adj _ _ (ringOne R) (ringOne S) g
      apply (cancel_epi (Functor.LaxMonoidal.ε L)).1
      dsimp only [g]
      have hu : (Functor.LaxMonoidal.ε L ≫ L.map (ringOne R)) ≫ eR.inv =
          ringOne A := IsMonHom.one_hom eR.inv
      simp only [← Category.assoc]
      rw [hu, ringMap_one]
      simp only [← Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory,
        Functor.Monoidal.ε_η, Category.id_comp]
    · apply adjunct_binary L V adj _ _ (ringMul R) (ringMul S) g
      dsimp only [g]
      rw [← Category.assoc, binary_inverse L _ _ eR _ _
        ((binary_transport_iff L _ _ eR (ringMul R) (ringMul A)).1 hmul)]
      rw [Category.assoc, Category.assoc, ringMap_mul]
      simp only [← Category.assoc, tensorHom_comp_tensorHom]
  let I := imageFunctor L R A eR.hom haI hmI
  let P := imageFunctor V S R d haP hmP
  refine ⟨I, P, imageFunctorUnderlying L R A eR.hom haI hmI,
    imageFunctorUnderlying V S R d haP hmP, ?_, ?_⟩
  · intro M
    refine ⟨fromProd _ _ ≫ addition R M, fromProd _ _ ≫ action R M,
      fromProd _ _ ≫ addition A (I.obj M), fromProd _ _ ≫ action A (I.obj M),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro W x; rfl
    · intro W x; rfl
    · intro W x; rfl
    · intro W x; rfl
    · change L.map (fromProd _ _ ≫ addition R M) = prodComparison L _ _ ≫
        prod.map (𝟙 (L.obj ((mset R).obj M))) (𝟙 _) ≫
          (fromProd _ _ ≫ addition A (imageModule L R A eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [prod.map_id_id, Category.id_comp, Category.comp_id]
      exact imageModule_addition_comparison L R A eR.hom haI hmI M
    · change L.map (fromProd _ _ ≫ action R M) = prodComparison L _ _ ≫
        prod.map eR.inv (𝟙 (L.obj ((mset R).obj M))) ≫
          (fromProd _ _ ≫ action A (imageModule L R A eR.hom haI hmI M)) ≫ 𝟙 _
      simp only [Category.comp_id]
      exact imageModule_action_comparison L R A eR haI hmI M
  · intro H
    let k := prod.map d (𝟙 (V.obj ((mset S).obj H))) ≫
      inv (prodComparison V (rset S) ((mset S).obj H))
    refine ⟨fromProd _ _ ≫ addition S H, fromProd _ _ ≫ action S H,
      fromProd _ _ ≫ addition R (P.obj H), fromProd _ _ ≫ action R (P.obj H), k,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro W x; rfl
    · intro W x; rfl
    · intro W x; rfl
    · intro W x; rfl
    · change V.map (fromProd _ _ ≫ addition S H) = prodComparison V _ _ ≫
        prod.map (𝟙 (V.obj ((mset S).obj H))) (𝟙 _) ≫
          (fromProd _ _ ≫ addition R (imageModule V S R d haP hmP H)) ≫ 𝟙 _
      simp only [prod.map_id_id, Category.id_comp, Category.comp_id]
      exact imageModule_addition_comparison V S R d haP hmP H
    · dsimp only [k]
      simp only [Category.assoc, inv_prodComparison_map_fst, prod.map_fst]
      rfl
    · dsimp only [k]
      simp only [Category.assoc, inv_prodComparison_map_snd, prod.map_snd, Category.comp_id]
      rfl
    · exact imageModule_action_comparison_right V S R d haP hmP H


/-- Construct the module direct image from a structural ring map.

Source: Stacks Project, Modules on Sites, pushforward of modules on ringed topoi.
(auxiliary; not a blueprint node).
The underlying sheaf is literally the given direct image. The scalar action is
restriction along the adjunct of the structural map, and the Hom adjunction
transports this action and addition to those of the original module. -/
theorem ringData_inducedModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (g : CategoryTheory.RingedToposMorphism.RingData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    Nonempty g.Modules := by
  let L := g.inverse
  let V := g.direct
  let adj := g.adj
  let : PreservesFiniteLimits L := g.leftExact
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let : V.Braided := Functor.Braided.ofChosenFiniteProducts V
  let d := adj.homEquiv (rset B) (rset A) g.ringMap
  have hb (a : rset B ⊗ rset B ⟶ rset B) (b : rset A ⊗ rset A ⟶ rset A)
      (h : L.map a ≫ g.ringMap = CartesianMonoidalCategory.prodComparison L _ _ ≫
        (g.ringMap ⊗ₘ g.ringMap) ≫ b) :
      a ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫ V.map b :=
    adjunct_binary L V adj _ _ a b g.ringMap h
  have ha : ringAdd B ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd A) := by
    apply hb
    ext U t
    exact g.ring_add _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringAdd B) (fun _ _ ↦ rfl) U t
  have hm : let := ringMonoid A
            let := ringMonoid B
            let := V.monObjObj (rset A)
            IsMonHom d := by
    let := ringMonoid A
    let := ringMonoid B
    let := V.monObjObj (rset A)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant L V adj _ _ (ringOne B) (ringOne A) g.ringMap
      ext U t
      exact g.ring_one _ (ringOne B) (fun _ _ ↦ rfl) U t
    · apply hb
      ext U t
      exact g.ring_mul _ (CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.snd _ _) (ringMul B) (fun _ _ ↦ rfl) U t
  let P := imageFunctor V A B d ha hm
  refine ⟨{ modules := P
            additive := ?_
            underlying := imageFunctorUnderlying V A B d ha hm
            module_linear := ?_ }⟩
  · constructor
    intro M N f h
    ext W t
    have hs : (mset A).map (f + h) = CartesianMonoidalCategory.lift
        ((mset A).map f) ((mset A).map h) ≫ addition A N := by
      ext U x
      rfl
    change (V.map ((mset A).map (f + h))).hom.app W t = _
    rw [hs, V.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro M T a x y z hz U t
    change T ⟶ V.obj ((mset A).obj M) at x y z
    have hs : z = CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift a x ≫ action B (P.obj M)) y ≫
          addition B (P.obj M) := by
      ext W v
      exact hz W v
    have haM : action B (P.obj M) =
        (d ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ V _ _ ≫ V.map (action A M) := rfl
    have haddM : addition B (P.obj M) =
        Functor.LaxMonoidal.μ V _ _ ≫ V.map (addition A M) := rfl
    have hz' : z = CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.lift (a ≫ d) x ≫
          (CartesianMonoidalCategory.prodComparisonIso V _ _).inv ≫
            V.map (action A M)) y ≫
        (CartesianMonoidalCategory.prodComparisonIso V _ _).inv ≫
          V.map (addition A M) := by
      rw [hs, haM, haddM]
      have hl : CartesianMonoidalCategory.lift a x ≫ (d ⊗ₘ 𝟙 _) =
          CartesianMonoidalCategory.lift (a ≫ d) x := by
        simpa only [Category.comp_id] using
          CartesianMonoidalCategory.lift_map a x d (𝟙 _)
      simp only [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
      rw [← Category.assoc (CartesianMonoidalCategory.lift a x), hl]
    have hc := adj.counit_binary (addition A M)
      (CartesianMonoidalCategory.lift (a ≫ d) x ≫
        (CartesianMonoidalCategory.prodComparisonIso V _ _).inv ≫
          V.map (action A M)) y
    have haction := adj.counit_pair (action A M) (a ≫ d) x
    rw [haction] at hc
    have hd : L.map (a ≫ d) ≫ adj.counit.app (rset A) = L.map a ≫ g.ringMap := by
      rw [L.map_comp, Category.assoc]
      congr 1
      exact (adj.homEquiv _ _).symm_apply_apply g.ringMap
    rw [hd] at hc
    have hzz : (adj.homEquiv T ((mset A).obj M)).symm z =
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.lift (L.map a ≫ g.ringMap)
            ((adj.homEquiv T ((mset A).obj M)).symm x) ≫ action A M)
          ((adj.homEquiv T ((mset A).obj M)).symm y) ≫ addition A M := by
      rw [hz']
      exact hc
    change ((adj.homEquiv T ((mset A).obj M)).symm (z ≫ 𝟙 _)).hom.app U t = _
    simp only [Category.comp_id]
    exact congrArg (fun k ↦ k.hom.app U t) hzz

end SheafOfModules
