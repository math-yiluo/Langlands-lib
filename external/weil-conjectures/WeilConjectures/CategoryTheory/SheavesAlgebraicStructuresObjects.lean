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
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRing

/-!
# Algebraic sheaves as internal algebraic objects

Source: Stacks Project, Section 00YR, quadruples before Proposition 00YV and its
sextuple description of rings; Lemmas 006J and 00W2
(blueprint: situation-conventions).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- Source: Stacks Project, Section 00YR (quadruples and sextuples), Lemmas 006J and 00W2
(blueprint: situation-conventions).

`CommGrp` uses multiplicative names for addition, zero and negation. The equations
of functors are strict inverse identities, not merely an equivalence. The `eqToIso`
components transport across the asserted equality of underlying sheaves, and the
section formulas specify the canonical operations. The inverse therefore recovers
these same section operations. `IsMonHom` expresses preservation of addition and
zero; the extra inverse equation explicitly includes negation. `IsRingHom` includes
addition, zero, multiplication and one; the extra negation equation includes the
remaining structure map. Sheaf morphisms are natural transformations throughout.

Proof:
1. Products are sectionwise: glue each component of a compatible family uniquely
   (00W2; situation-conventions). The empty product is the
   singleton sheaf. The universal property is def-weil-category-product. Equality
   of natural transformations and compositions are checked on sections.
2. For an abelian sheaf use sectionwise addition, zero and negation. Restriction
   homomorphisms make these natural; sectionwise axioms give the group-object laws.
   The underlying sets form a sheaf by
   situation-conventions. Homomorphisms preserve the maps.
3. Conversely evaluate the internal operations on sections: the internal equations
   give an abelian group at every object; naturality makes restrictions homomorphisms.
   Apply situation-conventions again. A structure-preserving
   natural transformation becomes a family of homomorphisms.
4. The constructions recover the exact same sections, restrictions and operations
   on objects, and the exact same maps on morphisms. They are strict inverse functors
   commuting with forgetting. This also proves the stated morphism criterion.
5. For rings repeat steps 2--4 with multiplication and one. Naturality makes
   restrictions ring homomorphisms; associativity, commutativity, unit and
   distributivity hold sectionwise if and only if they hold as sheaf-map equations.
   Ring homomorphisms preserve zero and negation as well as addition, multiplication
   and one (00YR, proof of 00YV, rings as sextuples). -/
theorem sheaves_algebraicStructures_objects
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    (∀ (F G : Sheaf J (Type (max u v w))) (U : Cᵒᵖ),
      (F ⊗ G).obj.obj U = (F.obj.obj U × G.obj.obj U)) ∧
    (∀ U : Cᵒᵖ,
      Subsingleton ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U) ∧
      Nonempty ((𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U)) ∧
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
              GrpObj.inv (X := (F.obj B).X))) ∧
    (∃ (F : Sheaf J CommRingCat.{max u v w} ⥤ CommRingObjCat (Sheaf J (Type (max u v w))))
        (G : CommRingObjCat (Sheaf J (Type (max u v w))) ⥤ Sheaf J CommRingCat.{max u v w})
        (hF : F ⋙ CommRingObjCat.forget _ = sheafCompose J (forget CommRingCat.{max u v w})),
      G ⋙ sheafCompose J (forget CommRingCat.{max u v w}) = CommRingObjCat.forget _ ∧
      F ⋙ G = 𝟭 (Sheaf J CommRingCat.{max u v w}) ∧
      G ⋙ F = 𝟭 (CommRingObjCat (Sheaf J (Type (max u v w)))) ∧
      (∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
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
            (1 : A.obj.obj U))) ∧
      (∀ (A B : Sheaf J CommRingCat.{max u v w})
          (α : (sheafCompose J (forget CommRingCat.{max u v w})).obj A ⟶
            (sheafCompose J (forget CommRingCat.{max u v w})).obj B),
        (∃ f : A ⟶ B, (sheafCompose J (forget CommRingCat.{max u v w})).map f = α) ↔
          IsRingHom (show (F.obj A).X ⟶ (F.obj B).X from
            (eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ∧
          AddGrpObj.neg (X := (F.obj A).X) ≫
              ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) =
            ((eqToIso hF).hom.app A ≫ α ≫ (eqToIso hF).inv.app B) ≫
              AddGrpObj.neg (X := (F.obj B).X))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F G U
    rfl
  · intro U
    constructor
    · change Subsingleton PUnit
      infer_instance
    · change Nonempty PUnit
      exact ⟨PUnit.unit⟩
  · exact sheavesAlgebraicStructuresAbelian J
  · exact sheavesAlgebraicStructuresRing J

end CategoryTheory
