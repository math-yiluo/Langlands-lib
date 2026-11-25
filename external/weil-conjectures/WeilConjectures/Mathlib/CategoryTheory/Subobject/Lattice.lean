/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# The image pushforward of subobjects preserves suprema

For a morphism `f : X ⟶ Y`, the functor `Subobject.«exists» f : Subobject X ⥤ Subobject Y`
sending a subobject to its image under `f` is left adjoint to `Subobject.pullback f`
(this is `Subobject.existsPullbackAdj`). Since both subobject lattices are partial orders,
this adjunction is a Galois connection, so `Subobject.«exists» f` preserves all suprema.

## Main results

- `CategoryTheory.Subobject.gc_exists_pullback`: the adjunction as a Galois connection.
- `CategoryTheory.Subobject.exists_obj_mono`: image pushforward is monotone.
- `CategoryTheory.Subobject.exists_obj_sup`: image pushforward preserves binary suprema.
- `CategoryTheory.Subobject.exists_obj_iSup`: image pushforward preserves arbitrary suprema.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C} [HasImages C] [HasPullbacks C]

/-- The adjunction `Subobject.existsPullbackAdj` between the (partially ordered) lattices of
subobjects, read as a Galois connection. -/
lemma gc_exists_pullback (f : X ⟶ Y) :
    GaloisConnection («exists» f).obj (pullback f).obj :=
  (existsPullbackAdj f).gc

/-- The image pushforward of subobjects is monotone. -/
lemma exists_obj_mono (f : X ⟶ Y) : Monotone («exists» f).obj :=
  (gc_exists_pullback f).monotone_l

section

variable [HasBinaryCoproducts C]

/-- The image pushforward of subobjects preserves binary suprema. -/
lemma exists_obj_sup (f : X ⟶ Y) (S T : Subobject X) :
    («exists» f).obj (S ⊔ T) = («exists» f).obj S ⊔ («exists» f).obj T :=
  (gc_exists_pullback f).l_sup

end

section

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasWidePullbacks.{w} C]
  [HasCoproducts.{w} C] [InitialMonoClass C]

/-- The image pushforward of subobjects preserves arbitrary suprema. -/
lemma exists_obj_iSup (f : X ⟶ Y) {ι : Type*} (S : ι → Subobject X) :
    («exists» f).obj (⨆ i, S i) = ⨆ i, («exists» f).obj (S i) :=
  (gc_exists_pullback f).l_iSup

end

end CategoryTheory.Subobject
