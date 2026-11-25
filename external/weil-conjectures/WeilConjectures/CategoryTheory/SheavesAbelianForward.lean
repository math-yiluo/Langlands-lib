/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Sectionwise abelian sheaves and commutative group objects

Source: Stacks Project, Section 00YR and Proposition 00YV.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Source: Stacks Project Section 00YR, abelian sheaves as quadruples before Proposition 00YV.
(blueprint: lem-weil-pbc-sheaf-abelian-forward)
Proof: retain the underlying set-valued sheaf and use pointwise addition, zero, and
negation as the internal multiplication, unit, and inverse. Restriction maps preserve
these operations, hence they are natural transformations. The group identities and
commutativity hold on each section and therefore hold as sheaf morphism equations.
On a morphism use its underlying natural transformation; additivity gives preservation
of multiplication and unit. Identities and composition are inherited from the
underlying sheaves. Forgetting recovers the original functor, and its equality
components give exactly the stated section formulas. Conversely, an internal morphism
preserves the pointwise unit and multiplication, so its components are additive
homomorphisms. Naturality gives a morphism of additive sheaves, whose image is the
original internal morphism; this proves fullness. -/
theorem sheavesAbelianForward
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∃ (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
        (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w})),
      F.Full ∧
      (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)))) := by
  let S := sheafCompose J (forget AddCommGrpCat.{max u v w})
  let obj (A : Sheaf J AddCommGrpCat.{max u v w}) :
      CommGrp (Sheaf J (Type (max u v w))) := by
    letI : GrpObj (S.obj A) := {
      one := ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : A.obj.obj U))
                naturality := by intro U V f; ext x; exact (A.obj.map f).hom.map_zero.symm }⟩
      mul := ⟨{ app := fun U ↦
                  ↾(fun x ↦ (show A.obj.obj U from x.1) + (show A.obj.obj U from x.2))
                naturality := by
                  intro U V f
                  ext x
                  exact ((A.obj.map f).hom.map_add _ _).symm }⟩
      one_mul := by ext U x; exact zero_add (show A.obj.obj U from x.2)
      mul_one := by ext U x; exact add_zero (show A.obj.obj U from x.1)
      mul_assoc := by ext U x; exact add_assoc (show A.obj.obj U from x.1.1) x.1.2 x.2
      inv := ⟨{ app := fun U ↦ ↾(fun x ↦ -(show A.obj.obj U from x))
                naturality := by intro U V f; ext x; exact (A.obj.map f).hom.map_neg _ |>.symm }⟩
      left_inv := by ext U x; exact neg_add_cancel (show A.obj.obj U from x)
      right_inv := by ext U x; exact add_neg_cancel (show A.obj.obj U from x) }
    exact { X := S.obj A
            comm := { mul_comm := by ext U x; exact add_comm (show A.obj.obj U from x.2) x.1 } }
  let F : Sheaf J AddCommGrpCat.{max u v w} ⥤
      CommGrp (Sheaf J (Type (max u v w))) := {
    obj := obj
    map := fun f ↦ InducedCategory.homMk (Grp.homMk'' (S.map f)
      (by ext U x; exact (f.hom.app U).hom.map_zero)
      (by ext U x; exact (f.hom.app U).hom.map_add _ _))
    map_id := by intro A; rfl
    map_comp := by intro A B D f g; rfl }
  have hF : F ⋙ CommGrp.forget _ = S := rfl
  have hfull : F.Full := by
    refine { map_surjective := ?_ }
    intro A B f
    let := (obj A).grp
    let := (obj B).grp
    let α := f.hom.hom.hom.hom
    let β : A.obj ⟶ B.obj := {
      app U := AddCommGrpCat.ofHom {
        toFun := fun a ↦ α.app U a
        map_zero' := by
          exact congrArg (fun k ↦ k.hom.app U PUnit.unit)
            (IsMonHom.one_hom (M := (F.obj A).X) (N := (F.obj B).X) f.hom.hom.hom)
        map_add' := fun a b ↦ by
          exact congrArg (fun k ↦ k.hom.app U (a, b))
            (IsMonHom.mul_hom f.hom.hom.hom) }
      naturality := by
        intro U V g
        ext a
        exact ConcreteCategory.congr_hom (α.naturality g) a }
    refine ⟨⟨β⟩, ?_⟩
    apply CommGrp.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    ext a
    rfl
  refine ⟨F, hF, hfull, ?_⟩
  intro A U
  exact ⟨fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

end CategoryTheory
