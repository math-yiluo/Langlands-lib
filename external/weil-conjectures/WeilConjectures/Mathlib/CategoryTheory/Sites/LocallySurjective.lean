/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local injectivity and surjectivity on a covering family

A morphism of presheaves which is injective (resp. surjective) on sections over every object
mapping to a member of a family covering the site is locally injective (resp. locally
surjective).

## Main results

- `CategoryTheory.Presheaf.isLocallyInjective_of_coversTop`
- `CategoryTheory.Presheaf.isLocallySurjective_of_coversTop`
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Presheaf

universe w' v' u' v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

/-- A morphism of presheaves which is injective on sections over every object mapping to a
member of a family `Y` covering the site is locally injective. -/
lemma isLocallyInjective_of_coversTop {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (hf : ∀ (V : C) (i : I), (V ⟶ Y i) → Function.Injective (f.app (op V))) :
    IsLocallyInjective J f where
  equalizerSieve_mem {U} x y h := by
    refine J.superset_covering ?_ (hY U.unop)
    rintro V g ⟨i, ⟨a⟩⟩
    refine hf V i a ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/-- A morphism of presheaves which is surjective on sections over every object mapping to a
member of a family `Y` covering the site is locally surjective. -/
lemma isLocallySurjective_of_coversTop {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (hf : ∀ (V : C) (i : I), (V ⟶ Y i) → Function.Surjective (f.app (op V))) :
    IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hY U)
    rintro V g ⟨i, ⟨a⟩⟩
    exact hf V i a _

end CategoryTheory.Presheaf
