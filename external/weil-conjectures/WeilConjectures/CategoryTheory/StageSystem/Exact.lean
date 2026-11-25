/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Const
public import WeilConjectures.CategoryTheory.StageSystem.Pretriangulated

/-!
# Exactness of functors out of the pair category of a triangulated stage system

Let `Φ_i : C i ⥤ D` be a coherent cocone of functors to a pretriangulated category, with
isomorphisms `T_{j/i} ⋙ Φ_j ≅ Φ_i`. If the `Φ_i` commute with the shifts and the isomorphisms
are compatible with these commutations, the induced functor
`CategoryTheory.StageSystem.descFunctor Φ ι coh : S.PairCategory ⥤ D` commutes with the shifts,
`(i, x)⟦a⟧ = (i, x⟦a⟧) ↦ Φ_i (x⟦a⟧) ≅ (Φ_i x)⟦a⟧`; if moreover the `Φ_i` are triangulated, so is
the induced functor, a distinguished triangle of the pair category being isomorphic to the image
of a distinguished triangle of some stage.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits Pretriangulated

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, HasShift (C i) ℤ] {S : StageSystem C}
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
  (Φ : ∀ i, C i ⥤ D) (ι : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ Φ j ≅ Φ i)
  (coh : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i),
      (Φ k).map ((S.assoc h h').hom.app x) ≫ (ι (h.trans h')).hom.app x =
        (ι h').hom.app ((S.T h).obj x) ≫ (ι h).hom.app x)

open PairCategory

omit [∀ i, HasShift (C i) ℤ] [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]
  [HasShift D ℤ] in
lemma descFunctor_map_mkHom {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) :
    (descFunctor Φ ι coh).map (mkHom n hX hY u) =
      (ι hX).inv.app X.obj ≫ (Φ n).map u ≫ (ι hY).hom.app Y.obj :=
  rfl

omit [∀ i, HasShift (C i) ℤ] [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]
  [HasShift D ℤ] in
lemma descFunctor_map_ι {i : I} {x y : C i} (f : x ⟶ y) :
    (descFunctor Φ ι coh).map ((S.ι i).map f) = (Φ i).map f :=
  show constEval.map ((Morphism.ofCocone Φ ι coh).functor.map ((S.ι i).map f)) = _ by
    rw [Morphism.functor_map_ι]
    rfl

variable [∀ i, (Φ i).CommShift ℤ] [∀ {i j : I} (h : i ≤ j), NatTrans.CommShift (ι h).hom ℤ]

omit [IsDirectedOrder I]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ] in
/-- The compatibility of `ι` with the commutations with the shifts, for the inverse. -/
lemma ι_inv_shift_comm {i n : I} (h : i ≤ n) (a : ℤ) (z : C i) :
    (ι h).inv.app (z⟦a⟧) ≫ (Φ n).map (((S.T h).commShiftIso a).hom.app z) ≫
        ((Φ n).commShiftIso a).hom.app ((S.T h).obj z) =
      ((Φ i).commShiftIso a).hom.app z ≫ ((ι h).inv.app z)⟦a⟧' := by
  have A := NatTrans.shift_app_comm (ι h).inv a z
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at A
  exact A.symm

/-- The commutation of the descended functor with the shifts. -/
noncomputable def descFunctorCommShiftIso (a : ℤ) :
    shiftFunctor S.PairCategory a ⋙ descFunctor Φ ι coh ≅
      descFunctor Φ ι coh ⋙ shiftFunctor D a :=
  NatIso.ofComponents (fun X ↦ ((Φ X.stage).commShiftIso a).app X.obj) (fun {X Y} f ↦ by
    induction f using hom_induction with
    | h n hX hY u =>
      have B := ((Φ n).commShiftIso a).hom.naturality u
      have A := NatTrans.shift_app_comm (ι hY).hom a Y.obj
      simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc,
        Functor.comp_map] at A B
      have key : (ι hX).inv.app (X.obj⟦a⟧) ≫ (Φ n).map (((S.T hX).commShiftIso a).hom.app X.obj ≫
          u⟦a⟧' ≫ ((S.T hY).commShiftIso a).inv.app Y.obj) ≫ (ι hY).hom.app (Y.obj⟦a⟧) ≫
          ((Φ Y.stage).commShiftIso a).hom.app Y.obj =
          ((Φ X.stage).commShiftIso a).hom.app X.obj ≫
            ((ι hX).inv.app X.obj ≫ (Φ n).map u ≫ (ι hY).hom.app Y.obj)⟦a⟧' := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← A]
        simp only [← Functor.map_comp_assoc, Functor.comp_obj, Iso.inv_hom_id_app,
          Category.comp_id]
        rw [Functor.map_comp, Category.assoc, reassoc_of% B,
          reassoc_of% (ι_inv_shift_comm Φ ι hX a X.obj)]
        simp only [Functor.map_comp, Category.assoc]
      simp only [Functor.comp_map, Iso.app_hom]
      erw [Morphism.functor_map_mkHom, descFunctor_map_mkHom, descFunctor_map_mkHom]
      dsimp only [shiftFunctor_eq, Morphism.functor_obj, shiftMorphism_Φ]
      simp only [Category.assoc]
      exact key)

set_option linter.unusedSectionVars false in
lemma descFunctorCommShiftIso_hom_app (a : ℤ) (X : S.PairCategory) :
    (descFunctorCommShiftIso Φ ι coh a).hom.app X = ((Φ X.stage).commShiftIso a).hom.app X.obj :=
  rfl

/-- The descended functor commutes with the shifts. -/
noncomputable instance descFunctor_commShift : (descFunctor Φ ι coh).CommShift ℤ where
  commShiftIso := descFunctorCommShiftIso Φ ι coh
  commShiftIso_zero := by
    ext X
    rw [descFunctorCommShiftIso_hom_app, Functor.CommShift.isoZero_hom_app,
      shiftFunctorZero_hom_app, descFunctor_map_ι, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app]
    rfl
  commShiftIso_add a b := by
    ext X
    rw [descFunctorCommShiftIso_hom_app, Functor.CommShift.isoAdd_hom_app,
      shiftFunctorAdd_hom_app, descFunctor_map_ι, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app]
    rfl

set_option linter.unusedSectionVars false in
lemma descFunctor_commShiftIso_hom_app (a : ℤ) (X : S.PairCategory) :
    ((descFunctor Φ ι coh).commShiftIso a).hom.app X =
      ((Φ X.stage).commShiftIso a).hom.app X.obj :=
  rfl

/-- The restriction of the descended functor to a stage is `Φ_i`, compatibly with the
commutations with the shifts. -/
instance (i : I) : NatTrans.CommShift (ιCompDescFunctorIso Φ ι coh i).hom ℤ where
  shift_comm a := by
    ext x
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app]
    rw [ι_commShiftIso_hom_app, descFunctor_commShiftIso_hom_app]
    dsimp [ιCompDescFunctorIso, ι_obj]
    simp

variable [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [∀ {i j : I} (h : i ≤ j), (S.T h).Additive] [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]
  [Nonempty I] [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [∀ i, (Φ i).IsTriangulated]

/-- The functor induced by a coherent cocone of triangulated functors is triangulated. -/
instance descFunctor_isTriangulated : (descFunctor Φ ι coh).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨i, D', hD', ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _ ((Φ i).map_distinguished _ hD') _
      ((descFunctor Φ ι coh).mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso (S.ι i) (descFunctor Φ ι coh)).symm.app D' ≪≫
        (Functor.mapTriangleIso (ιCompDescFunctorIso Φ ι coh i)).app D')

end StageSystem

end CategoryTheory
