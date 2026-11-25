/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Finite-prefix towers

The explicit towers and maps in Stacks Project, Tag 07KW, proof of Lemma 15.88.1.
(blueprint: lem-pc-roos-finite-prefix-construction).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- The tower whose level `n` is the product of the first `n + s` levels of `A`. 
(blueprint: lem-pc-roos-finite-prefix-construction)
-/
def roosPrefixTower (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of ((i : Fin (n.unop + s)) → A.obj (Opposite.op i.val))
  map {_n _m} f := AddCommGrpCat.ofHom
    { toFun := fun x i ↦ x ⟨i.val, lt_of_lt_of_le i.isLt (Nat.add_le_add_right
        (leOfHom f.unop) s)⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Coordinatewise maps on finite-prefix towers. 
(blueprint: lem-pc-roos-finite-prefix-construction)
-/
def roosPrefixFunctor (s : ℕ) :
    (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj := roosPrefixTower s
  map φ :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        { toFun := fun x i ↦ φ.app (Opposite.op i.val) (x i)
          map_zero' := by ext i; exact map_zero _
          map_add' := by intros; ext i; exact map_add _ _ _ }
      naturality := by intros; rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The augmentation sending a tower element to all its earlier images. 
(blueprint: lem-pc-roos-finite-prefix-construction)
-/
def roosPrefixInclusion :
    𝟭 (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⟶ roosPrefixFunctor 1 where
  app A :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        { toFun := fun x i ↦
            A.map (homOfLE (Nat.le_of_lt_succ i.isLt)).op x
          map_zero' := by ext i; exact map_zero _
          map_add' := by intros; ext i; exact map_add _ _ _ }
      naturality := by
        intro n m f
        ext x
        funext i
        change A.map ((homOfLE _).op) (A.map f x) = A.map ((homOfLE _).op) x
        rw [← ConcreteCategory.comp_apply, ← A.map_comp]
        rfl }
  naturality A B φ := by
    ext n x
    funext i
    exact ConcreteCategory.congr_hom (φ.naturality
      (homOfLE (Nat.le_of_lt_succ i.isLt)).op).symm x

/-- The finite-prefix difference map, with coordinate `xᵢ - fᵢ xᵢ₊₁`. 
(blueprint: lem-pc-roos-finite-prefix-construction)
-/
def roosPrefixProjection : roosPrefixFunctor 1 ⟶ roosPrefixFunctor 0 where
  app A :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        { toFun := fun x i ↦ x ⟨i.val, by omega⟩ -
            A.map (homOfLE (Nat.le_succ i.val)).op (x ⟨i.val + 1, by omega⟩)
          map_zero' := by ext i; simp
          map_add' := by intros; ext i; simp only [Pi.add_apply, map_add]; abel }
      naturality := by intros; rfl }
  naturality A B φ := by
    ext n x
    funext i
    symm
    change φ.app (Opposite.op i.val) (_ - _) = _ - _
    rw [map_sub]
    congr 1
    exact ConcreteCategory.congr_hom (φ.naturality
      (homOfLE (Nat.le_succ i.val)).op) _

/-- The finite-prefix difference vanishes on compatible tuples. 
(blueprint: lem-pc-roos-finite-prefix-construction)
-/
theorem roosPrefixInclusion_projection (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    roosPrefixInclusion.app A ≫ roosPrefixProjection.app A = 0 := by
  ext n x
  funext i
  change A.map ((homOfLE _).op) x -
    A.map ((homOfLE _).op) (A.map ((homOfLE _).op) x) = 0
  rw [← ConcreteCategory.comp_apply, ← A.map_comp]
  exact sub_self _

private theorem prefixProjection_surjective (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    Function.Surjective ((roosPrefixProjection.app A).app (Opposite.op n)) := by
  intro y
  change (i : Fin n) → A.obj (Opposite.op i.val) at y
  let x : (i : Fin (n + 1)) → A.obj (Opposite.op i.val) :=
    Fin.reverseInduction 0 (fun i z ↦
      y i + A.map (homOfLE (Nat.le_succ i.val)).op z)
  refine ⟨x, ?_⟩
  funext i
  change Fin n at i
  change x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ -
    A.map (homOfLE (Nat.le_succ i.val)).op (x i.succ) = y i
  have h := @Fin.reverseInduction_castSucc n
    (fun i ↦ A.obj (Opposite.op i.val)) 0
    (fun i z ↦ y i + A.map (homOfLE (Nat.le_succ i.val)).op z) i
  change x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
    y i + A.map (homOfLE (Nat.le_succ i.val)).op (x i.succ) at h
  rw [h]
  exact add_sub_cancel_right _ _

private theorem prefixInclusion_injective (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    Function.Injective ((roosPrefixInclusion.app A).app (Opposite.op n)) := by
  intro x y h
  have he := congrFun h (Fin.last n)
  change A.map (𝟙 (Opposite.op n)) x = A.map (𝟙 (Opposite.op n)) y at he
  simpa using he

private theorem prefixExact (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((ShortComplex.mk (roosPrefixInclusion.app A) (roosPrefixProjection.app A)
      (roosPrefixInclusion_projection A)).map
        ((evaluation ℕᵒᵖ AddCommGrpCat).obj (Opposite.op n))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  change (i : Fin (n + 1)) → A.obj (Opposite.op i.val) at x
  refine ⟨x (Fin.last n), ?_⟩
  funext i
  change A.map (homOfLE (Nat.le_of_lt_succ i.isLt)).op (x (Fin.last n)) = x i
  induction i using Fin.reverseInduction with
  | last =>
      change A.map (𝟙 (Opposite.op n)) _ = _
      simp
  | cast i ih =>
      have hi := congrFun hx i
      change x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ -
        A.map (homOfLE (Nat.le_succ i.val)).op (x i.succ) = 0 at hi
      rw [sub_eq_zero] at hi
      change x i.castSucc = _ at hi
      rw [hi, ← ih]
      exact (ConcreteCategory.congr_hom (A.map_comp
        (homOfLE (Nat.le_of_lt_succ i.succ.isLt)).op
        (homOfLE (Nat.le_succ i.val)).op) (x (Fin.last n)))

/-- The finite-prefix augmentation and difference form a short exact sequence.

Source: Stacks Project, Tag 07KW, proof of Lemma 15.88.1.
(blueprint: lem-pc-roos-finite-prefix-construction).

The augmentation is injective in its last coordinate. Downward induction identifies
its image with the kernel of the difference. Starting with last coordinate zero and
recursively setting `xᵢ = yᵢ + fᵢ(xᵢ₊₁)` proves surjectivity. Evaluation computes
homology in the functor category, so these levelwise statements give short exactness. -/
theorem roosPrefix_shortExact (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (ShortComplex.mk (roosPrefixInclusion.app A) (roosPrefixProjection.app A)
      (roosPrefixInclusion_projection A)).ShortExact := by
  let S := ShortComplex.mk (roosPrefixInclusion.app A) (roosPrefixProjection.app A)
    (roosPrefixInclusion_projection A)
  have hm : ∀ n, Mono ((roosPrefixInclusion.app A).app n) := fun n ↦
    (AddCommGrpCat.mono_iff_injective _).2 (prefixInclusion_injective A n.unop)
  have he : ∀ n, Epi ((roosPrefixProjection.app A).app n) := fun n ↦
    (AddCommGrpCat.epi_iff_surjective _).2 (prefixProjection_surjective A n.unop)
  refine { exact := ?_
           mono_f := NatTrans.mono_of_mono_app _
           epi_g := NatTrans.epi_of_epi_app _ }
  change S.Exact
  rw [ShortComplex.exact_iff_isZero_homology, Limits.IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  apply (Limits.IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).1 (prefixExact A n.unop))
    (S.mapHomologyIso ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).symm).eq_of_src

/-- Restriction of a finite prefix is surjective, including the empty prefix.

Source: Stacks Project, Tag 07KW, proof of Lemma 15.88.1.
(blueprint: lem-pc-roos-finite-prefix-construction).

Extend the tuple by zero in every new coordinate. Restriction recovers the tuple. -/
theorem roosPrefix_transition_surjective (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) : Function.Surjective
      ((roosPrefixTower s A).map (homOfLE (Nat.le_succ n)).op) := by
  classical
  intro x
  refine ⟨fun i ↦ if h : i.val < n + s then x ⟨i.val, h⟩ else 0, ?_⟩
  funext i
  exact dite_eq_left i.isLt

end CategoryTheory
