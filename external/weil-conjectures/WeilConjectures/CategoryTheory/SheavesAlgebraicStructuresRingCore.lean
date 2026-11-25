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
import Mathlib.CategoryTheory.IsoCat
import WeilConjectures.CategoryTheory.SheafRingObjectsBijective

/-!
# Sectionwise ring objects and strict inverse functors

Source: Stacks Project, Section 00YR and Proposition 00YV,
`proposition-functoriality-algebraic-structures-topoi`.
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The five operations of a ring sheaf, with all diagrams checked on sections. -/
@[instance_reducible] private def ringStructure
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{max u v w}) :
    CommRingObj ((sheafCompose J (forget CommRingCat.{max u v w})).obj A) where
  zero := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : A.obj.obj U))
             naturality := by
               intro X Y f
               ext x
               change (0 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_zero _).symm }⟩
  add := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 + x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 + (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 + x.2)
              exact (map_add _ _ _).symm }⟩
  neg := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U ↦ -x)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X at x
              change -(A.obj.map f).hom x = (A.obj.map f).hom (-x)
              exact (map_neg _ _).symm }⟩
  one := ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : A.obj.obj U))
            naturality := by
               intro X Y f
               ext x
               change (1 : A.obj.obj Y) = (A.obj.map f).hom _
               exact (map_one _).symm }⟩
  mul := ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : A.obj.obj U × A.obj.obj U ↦ x.1 * x.2)
            naturality := by
              intro X Y f
              ext x
              change A.obj.obj X × A.obj.obj X at x
              change (A.obj.map f).hom x.1 * (A.obj.map f).hom x.2 =
                (A.obj.map f).hom (x.1 * x.2)
              exact (map_mul _ _ _).symm }⟩
  zero_add := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (0 : A.obj.obj U) + x.2 = x.2
    exact zero_add x.2
  add_zero := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) + 0 = x.1
    exact add_zero x.1
  add_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc x.1.1 x.1.2 x.2
  left_neg := by
    ext U x
    change A.obj.obj U at x
    change -(x : A.obj.obj U) + x = 0
    exact neg_add_cancel x
  right_neg := by
    ext U x
    change A.obj.obj U at x
    change (x : A.obj.obj U) + -x = 0
    exact add_neg_cancel x
  add_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) + x.1 = x.1 + x.2
    exact add_comm x.2 x.1
  one_mul := by
    ext U x
    change PUnit × A.obj.obj U at x
    change (1 : A.obj.obj U) * x.2 = x.2
    exact one_mul x.2
  mul_one := by
    ext U x
    change A.obj.obj U × PUnit at x
    change (x.1 : A.obj.obj U) * 1 = x.1
    exact mul_one x.1
  mul_assoc := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change (x.1.1 : A.obj.obj U) * x.1.2 * x.2 = x.1.1 * (x.1.2 * x.2)
    exact mul_assoc x.1.1 x.1.2 x.2
  mul_comm := by
    ext U x
    change A.obj.obj U × A.obj.obj U at x
    change (x.2 : A.obj.obj U) * x.1 = x.1 * x.2
    exact mul_comm x.2 x.1
  mul_add := by
    ext U x
    change A.obj.obj U × (A.obj.obj U × A.obj.obj U) at x
    change (x.1 : A.obj.obj U) * (x.2.1 + x.2.2) = x.1 * x.2.1 + x.1 * x.2.2
    exact mul_add x.1 x.2.1 x.2.2
  add_mul := by
    ext U x
    change (A.obj.obj U × A.obj.obj U) × A.obj.obj U at x
    change ((x.1.1 : A.obj.obj U) + x.1.2) * x.2 = x.1.1 * x.2 + x.1.2 * x.2
    exact add_mul x.1.1 x.1.2 x.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The sectionwise ring-object functor, retaining the underlying sheaf and maps. -/
private def forward
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) : Sheaf J CommRingCat.{max u v w} ⥤
    CommRingObjCat (Sheaf J (Type (max u v w))) where
  obj A :=
    { X := (sheafCompose J (forget CommRingCat.{max u v w})).obj A
      commRingObj := ringStructure J A }
  map {A B} f := by
    letI := ringStructure J A
    letI := ringStructure J B
    exact
    { hom := (sheafCompose J (forget CommRingCat.{max u v w})).map f
      isRingHom :=
        { zero_hom := by
            ext U x
            exact map_zero (f.hom.app U).hom
          add_hom := by
            ext U x
            change A.obj.obj U × A.obj.obj U at x
            exact map_add (f.hom.app U).hom x.1 x.2
          one_hom := by
            ext U x
            exact map_one (f.hom.app U).hom
          mul_hom := by
            ext U x
            change A.obj.obj U × A.obj.obj U at x
            exact map_mul (f.hom.app U).hom x.1 x.2 } }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Internal ring homomorphisms give natural families of ring homomorphisms. -/
private theorem forward_full
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) : (forward J).Full where
  map_surjective {A B} f := by
    let α : A.obj ⋙ forget CommRingCat ⟶ B.obj ⋙ forget CommRingCat := f.hom.hom
    let β : A.obj ⟶ B.obj :=
      { app U := CommRingCat.ofHom
          { toFun := fun a ↦ α.app U a
            map_zero' := by
              have h := congrArg (fun k ↦ k.hom.app U PUnit.unit)
                (IsAddMonHom.zero_hom f.hom)
              exact h
            map_add' a b := by
              have h := congrArg (fun k ↦ k.hom.app U (a, b))
                (IsAddMonHom.add_hom f.hom)
              exact h
            map_one' := by
              have h := congrArg (fun k ↦ k.hom.app U PUnit.unit)
                (IsMonHom.one_hom f.hom)
              exact h
            map_mul' a b := by
              have h := congrArg (fun k ↦ k.hom.app U (a, b))
                (IsMonHom.mul_hom f.hom)
              exact h }
        naturality := by
          intro U V g
          ext a
          exact ConcreteCategory.congr_hom (α.naturality g) a }
    refine ⟨⟨β⟩, ?_⟩
    apply CommRingObjCat.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    ext a
    rfl


/-- Sectionwise ring structures and their strict inverse construction.
(blueprint: lem-weil-pbc-sheaf-algebraic-structures-ring-core)
Source: Stacks Project Section 00YR, rings as sextuples in Proposition 00YV.

Proof in words:
1. Keep the underlying sheaf of sets of a ring sheaf. Define addition and
   multiplication on the sectionwise product by the existing section operations;
   define zero and one on the singleton sheaf, and negation sectionwise.
   Restrictions preserve each operation. Ring identities on sections give all
   ring-object diagrams, including commutativity and distributivity. Send a
   ring-sheaf morphism to its underlying natural transformation.
2. Conversely, on each section set of an internal commutative ring object,
   evaluate its five operation maps (using the unique singleton section for
   constants). Evaluation of its diagrams gives the commutative ring axioms.
   Naturality makes restrictions ring homomorphisms. The underlying set presheaf
   is the original sheaf, so Presheaf.isSheaf_iff_isSheaf_forget makes this a ring
   sheaf. Evaluate ring-object morphisms to obtain natural ring homomorphisms.
3. Both constructions keep section sets and underlying maps. Each round trip
   recovers every operation pointwise; extensionality identifies the operation
   maps and the structures, while proof irrelevance identifies axiom and sheaf
   witnesses. Functor extensionality yields the four asserted strict equalities.
   The chosen equality hF transports the unchanged underlying sets, giving all
   five displayed operation formulas. -/
theorem sheavesAlgebraicStructuresRing_core
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
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
            (1 : A.obj.obj U)))) := by
  let F := forward J
  have hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}) := rfl
  have hops : ∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
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
            (1 : A.obj.obj U)) := by
    intro A U
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
  let : F.Full := forward_full J
  let : F.Faithful := hF.faithful_of_comp
  let : F.IsIso := ⟨inferInstance, inferInstance, sheafRingObjects_bijective.{u, v, w} J F hF hops⟩
  let e := F.asIsomorphism
  refine ⟨F, e.inverse, hF, ?_, e.unit_eq.symm, e.counit_eq, hops⟩
  calc
    e.inverse ⋙ sheafCompose J (forget CommRingCat.{max u v w}) =
        e.inverse ⋙ (F ⋙ CommRingObjCat.forget _) := by rw [hF]
    _ = (e.inverse ⋙ F) ⋙ CommRingObjCat.forget _ := (Functor.assoc _ _ _).symm
    _ = CommRingObjCat.forget _ := by
      change (e.inverse ⋙ e.functor) ⋙ _ = _
      rw [e.counit_eq, Functor.id_comp]

end CategoryTheory
