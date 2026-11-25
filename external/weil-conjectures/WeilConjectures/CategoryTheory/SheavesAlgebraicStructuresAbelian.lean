/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Ring.Limits

import WeilConjectures.CategoryTheory.SheavesAbelianForward
import WeilConjectures.CategoryTheory.SheafAbelianObjectsBijective
import Mathlib.CategoryTheory.IsoCat

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Intermediate algebraic-object equivalence component.
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-abelian-component)
Source: Stacks Project Section 00YR, quadruple description and Proposition 00YV.
The construction of sectionwise abelian-group objects and its inverse, including
the morphism criterion, is proved by evaluating structure maps on sections and
using the sheaf condition for underlying sets. -/
theorem sheavesAlgebraicStructuresAbelian
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∃ (F : Sheaf J AddCommGrpCat.{max u v w} ⥤ CommGrp (Sheaf J (Type (max u v w))))
        (G : CommGrp (Sheaf J (Type (max u v w))) ⥤ Sheaf J AddCommGrpCat.{max u v w})
        (hF : F ⋙ CommGrp.forget _ = sheafCompose J (forget AddCommGrpCat.{max u v w})),
      G ⋙ sheafCompose J (forget AddCommGrpCat.{max u v w}) = CommGrp.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J AddCommGrpCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommGrp (Sheaf J (Type (max u v w)))) ∧
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
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a))) ∧
      (∀ (A B : Sheaf J AddCommGrpCat.{max u v w})
          (α : (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget AddCommGrpCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget AddCommGrpCat.{max u v w})).map f = α) ↔
          IsMonHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          GrpObj.inv (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              GrpObj.inv (X := (F.obj B).X))) := by
  obtain ⟨F, hF, hfull, hsections⟩ := sheavesAbelianForward.{u, v, w} J
  have : F.Full := hfull
  have : F.Faithful := hF.faithful_of_comp
  have : F.IsIso := ⟨inferInstance, inferInstance,
    sheafAbelianObjects_bijective J F hF hsections⟩
  let e := F.asIsomorphism
  let G := e.inverse
  have hFG : F ⋙ G = 𝟭 _ := e.unit_eq.symm
  have hGF : G ⋙ F = 𝟭 _ := e.counit_eq
  have hG : G ⋙ sheafCompose J (forget AddCommGrpCat.{max u v w}) =
      CommGrp.forget _ := by
    rw [← hF, ← Functor.assoc, hGF, Functor.id_comp]
  refine ⟨F, G, hF, hG, hFG, hGF, hsections, ?_⟩
  intro A B α
  let β : (F.obj A).X ⟶ (F.obj B).X :=
    (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B
  have hβ (f : A ⟶ B)
      (hf : (sheafCompose J (forget AddCommGrpCat.{max u v w})).map f = α) :
      β = (CommGrp.forget _).map (F.map f) := by
    dsimp [β]
    rw [← hf]
    have hn := (eqToIso hF).hom.naturality f
    simpa using (congrArg (fun k ↦ k ≫ (eqToIso hF).inv.app B) hn).symm
  constructor
  · rintro ⟨f, hf⟩
    change IsMonHom β ∧ GrpObj.inv ≫ β = β ≫ GrpObj.inv
    rw [hβ f hf]
    change IsMonHom (F.map f).hom.hom.hom ∧ _
    exact ⟨inferInstance, GrpObj.inv_hom (F.map f).hom.hom.hom⟩
  · rintro ⟨hm, _⟩
    have : IsMonHom β := hm
    let g : F.obj A ⟶ F.obj B := InducedCategory.homMk (Grp.homMk β)
    refine ⟨F.preimage g, ?_⟩
    have hn := (eqToIso hF).hom.naturality (F.preimage g)
    have hg : (CommGrp.forget _).map (F.map (F.preimage g)) = β := by
      rw [F.map_preimage]
      rfl
    change (CommGrp.forget _).map (F.map (F.preimage g)) ≫
        (eqToIso hF).hom.app B =
      (eqToIso hF).hom.app A ≫
        (sheafCompose J (forget AddCommGrpCat.{max u v w})).map (F.preimage g) at hn
    rw [hg] at hn
    have := congrArg (fun k ↦ (eqToIso hF).inv.app A ≫ k) hn
    simpa [β] using this.symm

end CategoryTheory
