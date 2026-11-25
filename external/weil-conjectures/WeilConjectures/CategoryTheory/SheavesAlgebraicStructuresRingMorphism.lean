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

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Strict inverse functors over the underlying sheaf functor give the morphism criterion.
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-ring-morphism)
Source: Stacks Project Section 00YR and Proposition 00YV, structure-preserving morphisms.

Proof in words: the identity G ⋙ F makes G faithful; the identity F ⋙ G then
makes F full. Naturality of eqToIso hF identifies the underlying map of F.map f
with the conjugate of the underlying map of f. Thus a lift gives an IsRingHom,
and Mathlib's AddGrpObj.neg_comp supplies compatibility with negation.
Conversely package an IsRingHom as a CommRingObjCat morphism and use fullness of
F to lift it. Conjugating the map_preimage equality back gives exactly the
requested underlying map. Neither h₁ nor operation formulas are needed. -/
theorem sheavesAlgebraicStructuresRing_morphism
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J CommRingCat.{max u v w} ⥤
      CommRingObjCat (Sheaf J (Type (max u v w))))
    (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤
      Sheaf J CommRingCat.{max u v w})
    (hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}))
    (_h₁ : G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) =
      CommRingObjCat.forget _)
    (h₂ : F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}))
    (h₃ : G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w))))) :
    ∀ (A B : Sheaf J CommRingCat.{max u v w})
      (α : (sheafCompose J (forget CommRingCat.{max u v w})).obj A ⟶
        (sheafCompose J (forget CommRingCat.{max u v w})).obj B),
      (∃ f : A ⟶ B, (sheafCompose J (forget CommRingCat.{max u v w})).map f = α) ↔
        IsRingHom (show (F.obj A).X ⟶ (F.obj B).X from
          (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
        AddGrpObj.neg (X := (F.obj A).X) ≫
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
          ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
            AddGrpObj.neg (X := (F.obj B).X) := by
  let : G.Faithful := Functor.Faithful.of_comp_eq h₃
  let : (F ⋙ G).Full := h₂.symm ▸ inferInstanceAs (𝟭 _).Full
  let : F.Full := Functor.Full.of_comp_faithful F G
  intro A B α
  let β : (F.obj A).X ⟶ (F.obj B).X :=
    (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B
  have map_eq (f : A ⟶ B) :
      (F.map f).hom = (eqToIso hF).hom.app A ≫
        (sheafCompose J (forget CommRingCat.{max u v w})).map f ≫
        (eqToIso hF).inv.app B := by
    have h := (eqToIso hF).hom.naturality f
    simpa using congrArg (fun k => k ≫ (eqToIso hF).inv.app B) h
  constructor
  · rintro ⟨f, rfl⟩
    rw [← map_eq f]
    refine ⟨inferInstance, ?_⟩
    simpa only [Hom.neg_def, Category.id_comp] using
      (AddGrpObj.neg_comp (𝟙 (F.obj A).X) (F.map f).hom)
  · rintro ⟨h, _⟩
    let : IsRingHom β := h
    let b : F.obj A ⟶ F.obj B := ⟨β⟩
    refine ⟨F.preimage b, ?_⟩
    have hm := congrArg CommRingObjCat.Hom.hom (F.map_preimage b)
    rw [map_eq] at hm
    have he := congrArg (fun k => (eqToIso hF).inv.app A ≫ k ≫
      (eqToIso hF).hom.app B) hm
    simpa [b, β] using he


end CategoryTheory
