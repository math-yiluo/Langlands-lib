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

@[instance_reducible]
private def sectionGroup
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : CommGrp (Sheaf J (Type (max u v w)))) (U : Cᵒᵖ) :
    AddCommGroup (R.X.obj.obj U) :=
  let : Zero (R.X.obj.obj U) := ⟨(MonObj.one (X := R.X)).hom.app U PUnit.unit⟩
  let : Add (R.X.obj.obj U) := ⟨fun a b => (MonObj.mul (X := R.X)).hom.app U (a, b)⟩
  let : Neg (R.X.obj.obj U) := ⟨fun a => (GrpObj.inv (X := R.X)).hom.app U a⟩
  { add a b := (MonObj.mul (X := R.X)).hom.app U (a, b)
    zero := (MonObj.one (X := R.X)).hom.app U PUnit.unit
    neg a := (GrpObj.inv (X := R.X)).hom.app U a
    add_assoc a b c := by
      exact congrArg (fun f => f.hom.app U ((a, b), c)) (MonObj.mul_assoc R.X)
    zero_add a := by
      exact congrArg (fun f => f.hom.app U (PUnit.unit, a)) (MonObj.one_mul R.X)
    add_zero a := by
      exact congrArg (fun f => f.hom.app U (a, PUnit.unit)) (MonObj.mul_one R.X)
    neg_add_cancel a := by
      exact congrArg (fun f => f.hom.app U a) (GrpObj.left_inv R.X)
    add_comm a b := by
      exact congrArg (fun f => f.hom.app U (b, a)) (IsCommMonObj.mul_comm R.X)
    nsmul := nsmulRec
    zsmul := zsmulRec }

private def reconstructPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : CommGrp (Sheaf J (Type (max u v w)))) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  let : ∀ U : Cᵒᵖ, AddCommGroup (R.X.obj.obj U) := sectionGroup R
  { obj U := AddCommGrpCat.of (R.X.obj.obj U)
    map f := AddCommGrpCat.ofHom
      { toFun := R.X.obj.map f
        map_zero' := by
          exact (congrArg (fun g => g PUnit.unit)
            ((MonObj.one (X := R.X)).hom.naturality f)).symm
        map_add' a b := by
          exact (congrArg (fun g => g (a, b))
            ((MonObj.mul (X := R.X)).hom.naturality f)).symm }
    map_id U := by
      ext a
      exact congrArg (fun f => f a) (R.X.obj.map_id U)
    map_comp f g := by
      ext a
      exact congrArg (fun f => f a) (R.X.obj.map_comp f g) }

private def reconstructSheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : CommGrp (Sheaf J (Type (max u v w)))) :
    Sheaf J AddCommGrpCat.{max u v w} :=
  ⟨reconstructPresheaf R,
    (Presheaf.isSheaf_iff_isSheaf_comp J _
      (forget AddCommGrpCat.{max u v w})).2 R.X.property⟩

private theorem reconstructSheaf_forget
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : CommGrp (Sheaf J (Type (max u v w)))) :
    (sheafCompose J (forget AddCommGrpCat)).obj (reconstructSheaf R) = R.X := by
  rfl

private theorem commGrp_eq_of_mul
    {D : Type*} [Category* D] [CartesianMonoidalCategory D] [BraidedCategory D]
    (R S : CommGrp D) (hX : R.X = S.X)
    (hmul : MonObj.mul (X := R.X) ≫ eqToHom hX =
      (eqToHom hX ⊗ₘ eqToHom hX) ≫ MonObj.mul (X := S.X)) : R = S := by
  rcases R with ⟨X, g, c⟩
  rcases S with ⟨Y, g', c'⟩
  dsimp at hX
  subst Y
  rename_i g c g' c'
  have hg : g = g' := GrpObj.ext _ _ (MonObj.ext _ _ (by simpa using hmul))
  cases hg
  rfl

/-- Source: Stacks Project Section 00YR, quadruples and Proposition 00YV.
(blueprint: lem-weil-pbc-sheaf-abelian-objects-bijective-surjective)
Proof: for an internal commutative group object, evaluate multiplication, unit, and
inverse on every section. These operations give an additive commutative group by
evaluating the internal group identities, using that products and the terminal sheaf
are sectionwise. Naturality makes every restriction additive. The underlying sets
already form a sheaf, so `Presheaf.isSheaf_iff_isSheaf_comp` makes the algebraic
presheaf a sheaf as well. The construction keeps the underlying types and restriction
maps, giving a definitional equality after forgetting the additive structure.
Apply F to this explicitly constructed sheaf. The equality hF identifies its underlying
sheaf with the original one. Multiplication compatibility identifies the multiplications
after transporting along that equality. `MonObj.ext` identifies the monoid structures,
`GrpObj.ext` identifies the group structures, and proof irrelevance identifies the
commutativity witnesses. Thus the internal commutative group objects are equal. -/
theorem sheafAbelianObjects_surjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w}))
    (hsections : (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)))) :
    ∀ R : CommGrp (Sheaf J (Type (max u v w))), ∃ A, F.obj A = R := by
  intro R
  let A := reconstructSheaf R
  refine ⟨A, ?_⟩
  have hX : (F.obj A).X = R.X :=
    (Functor.congr_obj hF A).trans (reconstructSheaf_forget R)
  apply commGrp_eq_of_mul (F.obj A) R hX
  ext U ⟨a, b⟩
  have h := (hsections A U).1 a b
  change (eqToHom hX).hom.app U
      ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
    (MonObj.mul (X := R.X)).hom.app U
      ((eqToHom hX).hom.app U a, (eqToHom hX).hom.app U b)
  have he : (eqToIso hF).hom.app A = eqToHom hX := by
    simp only [eqToIso, eqToHom_app]
  rw [he] at h
  exact h

end CategoryTheory
