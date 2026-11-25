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
import Mathlib.Algebra.Group.Ext

/-!
# Sectionwise abelian sheaves and commutative group objects

Source: Stacks Project, Section 00YR and Proposition 00YV.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem sectionGroup_eq {X : Type w} (A B : AddCommGrpCat.{w})
    (eA : X = A.carrier) (eB : X = B.carrier) (m : X → X → X)
    (hA : ∀ a b, cast eA (m a b) = cast eA a + cast eA b)
    (hB : ∀ a b, cast eB (m a b) = cast eB a + cast eB b) : A = B := by
  obtain ⟨TA, gA⟩ := A
  obtain ⟨TB, gB⟩ := B
  dsimp at eA eB
  subst TA
  subst TB
  rename_i gA gB
  have hg : gA = gB := AddCommGroup.ext (funext fun a ↦ funext fun b ↦
    (hA a b).symm.trans (hB a b))
  cases hg
  rfl

private theorem section_cast {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : Sheaf J (Type w)}
    (e : P = Q) (U : Cᵒᵖ) (a : P.obj.obj U) :
    (eqToHom e).hom.app U a = cast (congrArg (fun S ↦ S.obj.obj U) e) a := by
  subst Q
  rfl

private theorem section_mul_cast {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {P Q : CommGrp (Sheaf J (Type (max u v w)))}
    (e : P = Q) (U : Cᵒᵖ) (a b : P.X.obj.obj U) :
    cast (congrArg (fun S ↦ S.X.obj.obj U) e)
        ((MonObj.mul (X := P.X)).hom.app U (a, b)) =
      (MonObj.mul (X := Q.X)).hom.app U
        (cast (congrArg (fun S ↦ S.X.obj.obj U) e) a,
          cast (congrArg (fun S ↦ S.X.obj.obj U) e) b) := by
  subst Q
  rfl

/-- Source: Stacks Project Section 00YR, quadruples and Proposition 00YV.
(blueprint: lem-weil-pbc-sheaf-abelian-objects-bijective-injective)
Proof: for an internal commutative group object, evaluate multiplication, unit, and
inverse on every section. These operations give an additive commutative group by
evaluating the internal group identities, using that products and the terminal sheaf
are sectionwise. Naturality makes every restriction additive. The underlying sets
already form a sheaf, so Presheaf.isSheaf_iff_isSheaf_forget makes the algebraic
presheaf a sheaf as well. No choice of a new underlying set is needed.
For surjectivity, apply F to the reconstructed sheaf. The section formulas identify
its three internal operations with the original operations, and hF identifies the
underlying sheaf. Extensionality and proof irrelevance give equality of objects.
For injectivity, an equality F(A)=F(B) identifies underlying sheaves through hF;
the section formulas identify their addition, zero and negation. Natural and integer
scalar multiplication and subtraction are determined by these operations and their
recursion laws. Thus the additive group structures agree. Restrictions agree by
extensionality of homomorphisms, and sheaf witnesses agree by proof irrelevance. -/
theorem sheafAbelianObjects_injective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w}))
    (hsections : (∀ (A : Sheaf J AddCommGrpCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U
              ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U
              ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U
              ((GrpObj.inv (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)))) :
    ∀ A B, F.obj A = F.obj B → A = B := by
  intro A B h
  have eA := Functor.congr_obj hF A
  have eB := Functor.congr_obj hF B
  have eX : (F.obj A).X = (F.obj B).X := congrArg CommGrp.X h
  have hobj : ∀ U, A.obj.obj U = B.obj.obj U := by
    intro U
    let EA : (F.obj A).X.obj.obj U = (A.obj.obj U).carrier :=
      congrArg (fun S ↦ S.obj.obj U) eA
    let EB : (F.obj A).X.obj.obj U = (B.obj.obj U).carrier :=
      congrArg (fun S ↦ S.obj.obj U) (eX.trans eB)
    apply sectionGroup_eq (A.obj.obj U) (B.obj.obj U) EA EB
      (fun a b ↦ ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)))
    · intro a b
      simpa only [eqToIso.hom, eqToHom_app, section_cast] using (hsections A U).1 a b
    · intro a b
      have hb := (hsections B U).1
        (cast (congrArg (fun S ↦ S.X.obj.obj U) h) a)
        (cast (congrArg (fun S ↦ S.X.obj.obj U) h) b)
      simp only [eqToIso.hom, eqToHom_app, section_cast] at hb
      rw [← section_mul_cast h U a b] at hb
      simpa only [cast_cast] using hb
  have hp : A.obj = B.obj := by
    refine Functor.ext hobj ?_
    intro U V f
    apply (forget AddCommGrpCat).map_injective
    have e : A.obj ⋙ forget AddCommGrpCat = B.obj ⋙ forget AddCommGrpCat :=
      congrArg (fun S ↦ S.obj) (eA.symm.trans (eX.trans eB))
    change (forget AddCommGrpCat).map (A.obj.map f) =
      (forget AddCommGrpCat).map
        (eqToHom (hobj U) ≫ B.obj.map f ≫ eqToHom (hobj V).symm)
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
    exact Functor.congr_hom e f
  cases A
  cases B
  cases hp
  rfl

end CategoryTheory
