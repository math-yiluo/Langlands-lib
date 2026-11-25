/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# The shift on the pair category of a stage system

Let `S` be a stage system on categories `C i` equipped with shifts by an additive monoid `A`,
such that the transition functors commute with the shifts (`Functor.CommShift`) and the
associators are compatible with these commutations (`NatTrans.CommShift`). In the application
these are the derived extensions of scalars `T_{F/E}` between the categories `D^b_c(T, E)`, with
their comparisons `σ_{F/E}`.

The shifts by `a : A` at all stages form a morphism of stage systems
`CategoryTheory.StageSystem.shiftMorphism S a`, and the descended functors define a shift on the
pair category: `(i, x)⟦a⟧ = (i, x⟦a⟧)`.
The stage inclusions `ι i` commute with the shifts, and so do the identifications
`T_{j/i} ⋙ ι j ≅ ι i`.

## Main definitions

- `CategoryTheory.StageSystem.shiftMorphism`: the shift by `a` as a morphism of stage systems.
- `CategoryTheory.StageSystem.PairCategory.hasShift`: the shift on the pair category.
- `CategoryTheory.StageSystem.ι_commShift`: the stage inclusions commute with the shifts.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (A : Type*) [AddMonoid A] [∀ i, HasShift (C i) A]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift A]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom A]

/-- The shifts by `a` at all the stages, as a morphism of stage systems: the compatibility with
the transition functors is given by the commutation isomorphisms of the transition functors with
the shifts. -/
@[simps]
noncomputable abbrev shiftMorphism (a : A) : Morphism S S where
  Φ i := shiftFunctor (C i) a
  β h := (S.T h).commShiftIso a
  coh h h' x := by
    simpa [Functor.commShiftIso_comp_hom_app] using
      NatTrans.shift_app_comm (S.assoc h h').hom a x

/-- The shift by `0` is the identity, as a compatible family of natural transformations. -/
@[simps]
noncomputable def shiftZeroHom : Morphism.Hom (S.shiftMorphism A 0) (Morphism.id S) where
  τ i := (shiftFunctorZero (C i) A).hom
  comm h x := by
    simp only [Morphism.id_β_hom_app]
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, Category.assoc,
      Functor.id_obj, Iso.inv_hom_id_app]

/-- The inverse of `shiftZeroHom`. -/
@[simps]
noncomputable def shiftZeroInvHom : Morphism.Hom (Morphism.id S) (S.shiftMorphism A 0) where
  τ i := (shiftFunctorZero (C i) A).inv
  comm h x := by
    simp only [Morphism.id_β_hom_app]
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
    exact (Category.id_comp _).symm

/-- The shift by `a + b` is the composite of the shifts, as a compatible family of natural
transformations. -/
@[simps]
noncomputable def shiftAddHom (a b : A) :
    Morphism.Hom (S.shiftMorphism A (a + b)) ((S.shiftMorphism A a).comp (S.shiftMorphism A b))
    where
  τ i := (shiftFunctorAdd (C i) a b).hom
  comm h x := by
    simp only [Morphism.comp_β_hom_app]
    simp [Functor.commShiftIso_add]

/-- The inverse of `shiftAddHom`. -/
@[simps]
noncomputable def shiftAddInvHom (a b : A) :
    Morphism.Hom ((S.shiftMorphism A a).comp (S.shiftMorphism A b)) (S.shiftMorphism A (a + b))
    where
  τ i := (shiftFunctorAdd (C i) a b).inv
  comm h x := by
    simp only [Morphism.comp_β_hom_app]
    simp [Functor.commShiftIso_add, ← Functor.map_comp_assoc]

variable [IsDirectedOrder I]

open PairCategory

namespace PairCategory

/-- The isomorphism between the descended shift by `0` and the identity functor. -/
noncomputable def shiftZeroIso : (S.shiftMorphism A 0).functor ≅ 𝟭 S.PairCategory :=
  NatIso.ofComponents (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorZero (C X.stage) A).app X.obj))
    (fun f ↦ by
      have := (Morphism.descNatTrans (S.shiftZeroHom A)).naturality f
      rw [Morphism.functor_id_map] at this
      exact this)

/-- The isomorphism between the descended shift by `a + b` and the composite of the descended
shifts. -/
noncomputable def shiftAddIso (a b : A) :
    (S.shiftMorphism A (a + b)).functor ≅
      (S.shiftMorphism A a).functor ⋙ (S.shiftMorphism A b).functor :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorAdd (C X.stage) a b).app X.obj))
    (fun f ↦ by
      have := (Morphism.descNatTrans (S.shiftAddHom A a b)).naturality f
      rw [Morphism.functor_comp_map] at this
      exact this)

/-- The data of the shift on the pair category, descended from the shifts at the stages. -/
noncomputable def shiftMkCore : ShiftMkCore S.PairCategory A where
  F a := (S.shiftMorphism A a).functor
  zero := shiftZeroIso S A
  add a b := shiftAddIso S A a b
  assoc_hom_app m₁ m₂ m₃ X := by
    have := congr_arg (S.ι X.stage).map (shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj)
    simp only [Functor.map_comp, shiftFunctorAdd', Iso.trans_hom, eqToIso.hom,
      NatTrans.comp_app, eqToHom_app, eqToHom_map, Category.assoc] at this
    dsimp only [shiftAddIso, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom]
    rw [Morphism.functor_map_ι]
    exact this
  zero_add_hom_app n X := by
    have := congr_arg (S.ι X.stage).map (shiftFunctorAdd_zero_add_hom_app n X.obj)
    simp only [Functor.map_comp, eqToHom_map] at this
    dsimp only [shiftAddIso, shiftZeroIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
      Iso.app_inv]
    rw [Morphism.functor_map_ι]
    exact this
  add_zero_hom_app n X := by
    have := congr_arg (S.ι X.stage).map (shiftFunctorAdd_add_zero_hom_app n X.obj)
    simp only [Functor.map_comp, eqToHom_map] at this
    dsimp only [shiftAddIso, shiftZeroIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
      Iso.app_inv]
    exact this

/-- The shift on the pair category: the shift of `(i, x)` is `(i, x⟦a⟧)`, and a morphism represented
by `u` at a stage `n` is shifted to the morphism represented by `u⟦a⟧`, up to the commutation
isomorphisms of the transition functors with the shifts. -/
noncomputable instance hasShift : HasShift S.PairCategory A :=
  hasShiftMk _ A (shiftMkCore S A)

variable {S A}

lemma shiftFunctor_eq (a : A) :
    shiftFunctor S.PairCategory a = (S.shiftMorphism A a).functor := rfl

@[simp]
lemma shiftFunctor_obj (a : A) (X : S.PairCategory) :
    (shiftFunctor S.PairCategory a).obj X = ⟨X.stage, (shiftFunctor (C X.stage) a).obj X.obj⟩ :=
  rfl

lemma shiftFunctor_map_mkHom (a : A) {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) :
    (shiftFunctor S.PairCategory a).map (mkHom n hX hY u) =
      mkHom (X := (shiftFunctor S.PairCategory a).obj X)
        (Y := (shiftFunctor S.PairCategory a).obj Y) n hX hY
        (((S.T hX).commShiftIso a).hom.app X.obj ≫ (shiftFunctor (C n) a).map u ≫
          ((S.T hY).commShiftIso a).inv.app Y.obj) := rfl

@[simp]
lemma shiftFunctor_map_ι (a : A) {i : I} {x y : C i} (f : x ⟶ y) :
    (shiftFunctor S.PairCategory a).map ((S.ι i).map f) =
      (S.ι i).map ((shiftFunctor (C i) a).map f) :=
  Morphism.functor_map_ι _ f

lemma shiftFunctorZero_hom_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory A).hom.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).hom.app X.obj) := rfl

lemma shiftFunctorZero_inv_app (X : S.PairCategory) :
    (shiftFunctorZero S.PairCategory A).inv.app X =
      (S.ι X.stage).map ((shiftFunctorZero (C X.stage) A).inv.app X.obj) := rfl

lemma shiftFunctorAdd_hom_app (a b : A) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).hom.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).hom.app X.obj) := rfl

lemma shiftFunctorAdd_inv_app (a b : A) (X : S.PairCategory) :
    (shiftFunctorAdd S.PairCategory a b).inv.app X =
      (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) a b).inv.app X.obj) := rfl

lemma shiftFunctorZero_inv_app_ι {i : I} (x : C i) :
    (shiftFunctorZero S.PairCategory A).inv.app ((S.ι i).obj x) =
      (S.ι i).map ((shiftFunctorZero (C i) A).inv.app x) := rfl

lemma shiftFunctorAdd_inv_app_ι (a b : A) {i : I} (x : C i) :
    (shiftFunctorAdd S.PairCategory a b).inv.app ((S.ι i).obj x) =
      (S.ι i).map ((shiftFunctorAdd (C i) a b).inv.app x) := rfl

end PairCategory

open PairCategory

variable {S A}

/-- The stage inclusions commute with the shifts, with identity commutation isomorphisms. -/
noncomputable instance ι_commShift (i : I) : (S.ι i).CommShift A where
  commShiftIso a := (Morphism.ιCompFunctorIso (S.shiftMorphism A a) i).symm
  commShiftIso_zero := by
    ext x
    simp [shiftFunctorZero_inv_app_ι, ← Functor.map_comp]
  commShiftIso_add a b := by
    ext x
    simp [shiftFunctorAdd_inv_app_ι, ← Functor.map_comp]

@[simp]
lemma ι_commShiftIso_hom_app (i : I) (a : A) (x : C i) :
    ((S.ι i).commShiftIso a).hom.app x = 𝟙 _ := rfl

@[simp]
lemma ι_commShiftIso_inv_app (i : I) (a : A) (x : C i) :
    ((S.ι i).commShiftIso a).inv.app x = 𝟙 _ := rfl

/-- The identifications `T_{j/i} ⋙ ι j ≅ ι i` commute with the shifts. -/
instance transIso_commShift {i j : I} (h : i ≤ j) : NatTrans.CommShift (S.transIso h).hom A where
  shift_comm a := by
    ext x
    have e := NatTrans.shift_app_comm (S.assoc h (le_refl j)).hom a x
    simp only [Functor.commShiftIso_comp_hom_app] at e
    simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app, ι_commShiftIso_hom_app,
      comp_id, transIso_hom_app, isoToStage, ι_map_eq (le_refl j),
      shiftFunctor_map_mkHom]
    rw [mkHom_comp_mkHom]
    congr 1
    simp only [Category.assoc, ι_obj] at e ⊢
    rw [reassoc_of% e]
    simp

end StageSystem

end CategoryTheory
