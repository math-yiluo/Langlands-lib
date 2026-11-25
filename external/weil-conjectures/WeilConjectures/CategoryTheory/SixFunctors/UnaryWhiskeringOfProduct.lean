/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Unary full faithfulness from product precomposition

Source: the diagonal argument for natural transformations; Stacks Categories 001C.
(blueprint: lem-sf-unary-whiskering-from-product).
-/

@[expose] public section
set_option autoImplicit false
universe a b c d e f
open CategoryTheory
namespace CategoryTheory.Functor

/-- Full faithfulness of product precomposition implies unary full faithfulness.
Source: Stacks Categories 001C, applied to projection and diagonal functors
(blueprint: lem-sf-unary-whiskering-from-product).
Proof: extend a transformation of unary restrictions to the product by the first
projection, lift it using ff, and restrict the lift to the diagonal. The
map-preimage equation follows by evaluating ff.map_preimage on diagonal objects.
Faithfulness follows by first extending an equality using the first projection,
applying ff.map_injective, then evaluating again on the diagonal. -/
noncomputable def unaryWhiskeringOfProduct
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    (E : Type e) [Category.{f} E] (L : C ⥤ D)
    (ff : ((whiskeringLeft (C × C) (D × D) E).obj (L.prod L)).FullyFaithful) :
    ((whiskeringLeft C D E).obj L).FullyFaithful := by
  let W := (whiskeringLeft C D E).obj L
  have : W.Faithful := ⟨by
    intro F G α β h
    have h' : Functor.whiskerLeft (CategoryTheory.Prod.fst D D) α =
        Functor.whiskerLeft (CategoryTheory.Prod.fst D D) β := by
      apply ff.map_injective
      ext X
      exact congrArg (fun t ↦ t.app X.1) h
    ext X
    exact congrArg (fun t ↦ t.app (X, X)) h'⟩
  let pre {F G : D ⥤ E} (α : L ⋙ F ⟶ L ⋙ G) : F ⟶ G :=
    let α' : (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ F ⟶
        (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ G :=
      { app := fun X ↦ α.app X.1
        naturality := fun _ _ g ↦ α.naturality g.1 }
    let β : CategoryTheory.Prod.fst D D ⋙ F ⟶ CategoryTheory.Prod.fst D D ⋙ G :=
      ff.preimage α'
    { app := fun X ↦ β.app (X, X)
      naturality := fun _ _ g ↦ β.naturality (Prod.mkHom g g) }
  have hpre {F G : D ⥤ E} (α : L ⋙ F ⟶ L ⋙ G) :
      Functor.whiskerLeft L (pre α) = α := by
    ext X
    exact congrArg (fun t ↦ t.app (X, X))
      (ff.map_preimage
        (show (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ F ⟶
            (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ G from
          { app := fun X ↦ α.app X.1
            naturality := fun _ _ g ↦ α.naturality g.1 }))
  exact { preimage := fun α ↦ pre α
          map_preimage := hpre
          preimage_map := fun α ↦ W.map_injective (hpre (W.map α)) }

end CategoryTheory.Functor
