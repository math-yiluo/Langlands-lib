/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Ring.Ext

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem type_transport {T S : Type w} (h : T = S) (a : T) :
    (eqToHom h) a = cast h a := by
  cases h
  rfl

private theorem cast_ring_add
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R S : CommRingObjCat (Sheaf J (Type (max u v w)))) (h : R = S)
    (U : Cᵒᵖ) (a b : R.X.obj.obj U) :
    cast (congrArg (fun R ↦ R.X.obj.obj U) h)
      ((AddMonObj.add (X := R.X)).hom.app U (a, b)) =
      (AddMonObj.add (X := S.X)).hom.app U
        (cast (congrArg (fun R ↦ R.X.obj.obj U) h) a,
          cast (congrArg (fun R ↦ R.X.obj.obj U) h) b) := by
  cases h
  rfl

private theorem cast_ring_mul
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R S : CommRingObjCat (Sheaf J (Type (max u v w)))) (h : R = S)
    (U : Cᵒᵖ) (a b : R.X.obj.obj U) :
    cast (congrArg (fun R ↦ R.X.obj.obj U) h)
      ((MonObj.mul (X := R.X)).hom.app U (a, b)) =
      (MonObj.mul (X := S.X)).hom.app U
        (cast (congrArg (fun R ↦ R.X.obj.obj U) h) a,
          cast (congrArg (fun R ↦ R.X.obj.obj U) h) b) := by
  cases h
  rfl

private theorem ring_eq (R S : CommRingCat.{w}) (T : Type w)
    (eR : T = R) (eS : T = S) (add mul : T → T → T)
    (haR : ∀ a b, cast eR (add a b) = cast eR a + cast eR b)
    (hmR : ∀ a b, cast eR (mul a b) = cast eR a * cast eR b)
    (haS : ∀ a b, cast eS (add a b) = cast eS a + cast eS b)
    (hmS : ∀ a b, cast eS (mul a b) = cast eS a * cast eS b) : R = S := by
  rcases R with ⟨R, iR⟩
  rcases S with ⟨S, iS⟩
  dsimp at eR eS
  cases eR
  cases eS
  rename_i iR iS
  have hi : iR = iS := CommRing.ext
    (funext fun a ↦ funext fun b ↦ (haR a b).symm.trans (haS a b))
    (funext fun a ↦ funext fun b ↦ (hmR a b).symm.trans (hmS a b))
  cases hi
  rfl

private theorem presheaf_eq {D : Type u} [Category.{v} D]
    (P Q : D ⥤ CommRingCat.{w})
    (h : P ⋙ forget CommRingCat = Q ⋙ forget CommRingCat)
    (ho : ∀ X, P.obj X = Q.obj X) : P = Q := by
  refine CategoryTheory.Functor.ext ho ?_
  intro X Y f
  apply (forget CommRingCat).map_injective
  change (forget CommRingCat).map (P.map f) =
    (forget CommRingCat).map (eqToHom (ho X)) ≫
      (forget CommRingCat).map (Q.map f) ≫
        (forget CommRingCat).map (eqToHom (ho Y).symm)
  have hX := eqToHom_map (forget CommRingCat) (ho X)
  have hY := eqToHom_map (forget CommRingCat) (ho Y).symm
  rw [hX, hY]
  have hm := (eqToHom h).naturality f
  have hm' := congrArg (fun k ↦ k ≫ eqToHom
    (CategoryTheory.Functor.congr_obj h Y).symm) hm
  simpa only [eqToHom_app, CategoryTheory.Functor.comp_map, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id] using hm'

/-- Injectivity component of internal ring-object reconstruction.
(blueprint: lem-weil-pbc-sheaf-ring-objects-injective)
Proof in words: Given equal internal objects, the underlying sheaves agree by `hF`.
The five transported sectionwise operations agree by `hops`, so addition, zero,
negation, multiplication, and one agree on every section. Ring structures,
restriction maps, and sheaf witnesses are then equal by extensionality and
proof irrelevance, yielding equality of the original sheaves of rings. -/
theorem sheafRingObjects_injective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J CommRingCat.{max u v w} ⥤
      CommRingObjCat (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}))
    (hops : ∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) :
    Function.Injective F.obj := by
  intro A B hAB
  have ht (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ)
      (a : (F.obj A).X.obj.obj U) :
      ((eqToIso hF).hom.app A).hom.app U a =
        cast (congrArg (fun G ↦ (G.obj A).obj.obj U) hF) a := by
    simp only [eqToIso.hom, eqToHom_app, ObjectProperty.eqToHom_hom]
    exact type_transport _ a
  have hP : A.obj ⋙ forget CommRingCat = B.obj ⋙ forget CommRingCat := by
    have h := congrArg (fun R : CommRingObjCat (Sheaf J (Type (max u v w))) ↦ R.X) hAB
    rw [show (F.obj A).X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A from
      CategoryTheory.Functor.congr_obj hF A,
      show (F.obj B).X = (sheafCompose J (forget CommRingCat.{max u v w})).obj B from
      CategoryTheory.Functor.congr_obj hF B] at h
    exact congrArg (fun S ↦ S.obj) h
  have ho (U : Cᵒᵖ) : A.obj.obj U = B.obj.obj U := by
    let T := (F.obj A).X.obj.obj U
    let eA : T = A.obj.obj U := congrArg (fun G ↦ (G.obj A).obj.obj U) hF
    let eB : T = B.obj.obj U := (congrArg
      (fun R : CommRingObjCat (Sheaf J (Type (max u v w))) ↦ R.X.obj.obj U) hAB).trans
        (congrArg (fun G ↦ (G.obj B).obj.obj U) hF)
    apply ring_eq (A.obj.obj U) (B.obj.obj U) T eA eB
      (fun a b ↦ (AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b))
      (fun a b ↦ (MonObj.mul (X := (F.obj A).X)).hom.app U (a, b))
    · intro a b
      simpa only [← ht] using (hops A U).1 a b
    · intro a b
      simpa only [← ht] using (hops A U).2.2.2.1 a b
    · intro a b
      have h := congrArg
        (cast (congrArg (fun G ↦ (G.obj B).obj.obj U) hF))
        (cast_ring_add J (F.obj A) (F.obj B) hAB U a b)
      have h' := (hops B U).1
        (cast (congrArg (fun R ↦ R.X.obj.obj U) hAB) a)
        (cast (congrArg (fun R ↦ R.X.obj.obj U) hAB) b)
      simp only [ht] at h'
      simpa only [cast_cast] using h.trans h'
    · intro a b
      have h := congrArg
        (cast (congrArg (fun G ↦ (G.obj B).obj.obj U) hF))
        (cast_ring_mul J (F.obj A) (F.obj B) hAB U a b)
      have h' := (hops B U).2.2.2.1
        (cast (congrArg (fun R ↦ R.X.obj.obj U) hAB) a)
        (cast (congrArg (fun R ↦ R.X.obj.obj U) hAB) b)
      simp only [ht] at h'
      simpa only [cast_cast] using h.trans h'
  have h := presheaf_eq A.obj B.obj hP ho
  cases A
  cases B
  cases h
  rfl

end CategoryTheory
