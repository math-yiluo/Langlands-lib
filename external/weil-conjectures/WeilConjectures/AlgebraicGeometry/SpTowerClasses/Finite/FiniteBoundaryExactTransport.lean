/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.UnderlyingSingleArrow
import all WeilConjectures.CategoryTheory.Derived.DerivedSingleConstantsComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
/-! # Exact transport of single-to-shifted-single arrows -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section
variable {C D H : Type*} [Category C] [Category D] [Category H]
  [Abelian C] [Abelian D] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory H]

/-- Exact single-arrow transport respects ordinary natural isomorphisms.
Source: localization naturality and compatibility on single complexes.
(blueprint: lem-sfb-exact-arrow-transport). -/
theorem mapSingleArrow_natIso (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) {X Y : C} (n : ℤ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    (DerivedCategory.singleFunctor D 0).map (e.hom.app X) ≫
        mapSingleArrow G n f =
      mapSingleArrow F n f ≫
        ((DerivedCategory.singleFunctor D 0).map (e.hom.app Y))⟦n⟧' := by
  let ed := Functor.mapDerivedCategoryNatIso e
  have hx : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ed.hom.app ((DerivedCategory.singleFunctor C 0).obj X) =
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app X := by
    apply (cancel_mono ((G.mapDerivedCategorySingleFunctor 0).hom.app X)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [Functor.single_nat F G e X]
    simp only [Iso.inv_hom_id_app_assoc]
    erw [Category.comp_id]
  simp only [mapSingleArrow, Category.assoc]
  rw [← reassoc_of% hx]
  rw [← ed.hom.naturality_assoc]
  rw [← NatTrans.shift_app_comm_assoc]
  simp only [← (shiftFunctor (DerivedCategory D) n).map_comp]
  rw [Functor.single_nat F G e Y]

/-- Successive exact transports equal transport by the composite functor.
Source: localization composition and compatibility on single complexes.
(blueprint: lem-sfb-exact-arrow-transport). -/
theorem mapSingleArrow_composite (F : C ⥤ D) (G : D ⥤ H) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} (n : ℤ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow G n (mapSingleArrow F n f) = mapSingleArrow (F ⋙ G) n f := by
  let e := (Functor.mapDerivedCategoryCompIso F G).symm
  have hx : (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).inv.app X ≫
        e.hom.app ((DerivedCategory.singleFunctor C 0).obj X) := by
    apply (cancel_mono (G.mapDerivedCategory.map
      ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X))).mp
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    dsimp only [e, Iso.symm_hom]
    rw [Functor.single_comp F G X]
    simp only [Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]; rfl
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [G.mapDerivedCategory.commShiftIso_hom_naturality_assoc]
  rw [reassoc_of% hx]
  have hn := ShiftedHom.map_naturality f e.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.map,
    Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc] at hn
  rw [← reassoc_of% hn]
  simp only [← (shiftFunctor (DerivedCategory H) n).map_comp]
  dsimp only [e, Iso.symm_hom]
  rw [Functor.single_comp F G Y]

/-- Exact transport preserves precomposition by an ordinary map.
Source: naturality of the single comparison (blueprint: lem-sfb-exact-arrow-transport). -/
theorem mapSingleArrow_precompose (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X X' Y : C} (a : X' ⟶ X) (n : ℤ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow F n ((DerivedCategory.singleFunctor C 0).map a ≫ f) =
      (DerivedCategory.singleFunctor D 0).map (F.map a) ≫ mapSingleArrow F n f := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

/-- Exact transport preserves postcomposition by a shifted ordinary map.
Source: naturality of the shift and single comparisons
(blueprint: lem-sfb-exact-arrow-transport). -/
theorem mapSingleArrow_postcompose (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Y' : C} (b : Y ⟶ Y') (n : ℤ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow F n (f ≫ ((DerivedCategory.singleFunctor C 0).map b)⟦n⟧') =
      mapSingleArrow F n f ≫
        ((DerivedCategory.singleFunctor D 0).map (F.map b))⟦n⟧' := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← Functor.map_comp, hn, Functor.map_comp]
/-- Evaluation, target identification and forgetting equal their exact composite.
Source: the definition and exact transport laws
(blueprint: lem-sfb-exact-arrow-transport). -/
theorem forgetEvaluatedArrow_eq (F : C ⥤ D) (G : D ⥤ H) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {Z : D} (e : F.obj Y ≅ Z)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    forgetEvaluatedArrow F G e f = mapSingleArrow (F ⋙ G) (2 : ℤ) f ≫
      ((DerivedCategory.singleFunctor H 0).map (G.map e.hom))⟦(2 : ℤ)⟧' := by
  unfold forgetEvaluatedArrow
  rw [mapSingleArrow_postcompose, mapSingleArrow_composite]

/-- An underlying arrow with endpoints transports by the exact composite.
Source: exact transport laws (blueprint: lem-sfb-exact-arrow-transport). -/
theorem map_underlyingSingleArrow (F : C ⥤ D) (G : D ⥤ H) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {X' Y' : D} (q : X' ⟶ F.obj X) (r : F.obj Y ⟶ Y')
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    mapSingleArrow G (2 : ℤ) (underlyingSingleArrow F q r f) =
      (DerivedCategory.singleFunctor H 0).map (G.map q) ≫
        mapSingleArrow (F ⋙ G) (2 : ℤ) f ≫
        ((DerivedCategory.singleFunctor H 0).map (G.map r))⟦(2 : ℤ)⟧' := by
  rw [underlyingSingleArrow, mapSingleArrow_precompose, mapSingleArrow_postcompose,
    mapSingleArrow_composite]

end
end AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
/-- Compose a naturality square with its two normalized endpoints.
Source: associativity and functoriality of shifts
(blueprint: lem-sfb-exact-arrow-transport). -/
theorem finiteBoundary_square_glue {D : Type*} [Category D] [HasShift D ℤ]
    {I X Y R S A B C Z : D} (n : ℤ)
    (p : I ⟶ X) (q : X ⟶ R) (r : Y ⟶ S) (eX : R ⟶ A) (eY : S ⟶ B)
    (t : B ⟶ C) (s : Y ≅ Z) (a : A ⟶ B⟦n⟧) (a₀ : R ⟶ S⟦n⟧)
    (f : X ⟶ Y⟦n⟧) (hc : q ≫ a₀ = f ≫ r⟦n⟧')
    (hn : eX ≫ a = a₀ ≫ eY⟦n⟧') :
    (p ≫ q ≫ eX) ≫ (a ≫ t⟦n⟧') =
      (p ≫ f ≫ s.hom⟦n⟧') ≫ (s.inv ≫ r ≫ eY ≫ t)⟦n⟧' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc]
  simp only [← (shiftFunctor D n).map_comp_assoc, Iso.hom_inv_id_assoc]
/-- Assemble a transported scalar square before specializing any module categories.
Source: exact single-arrow transport, naturality and square gluing.
(blueprint: lem-sfb-exact-arrow-transport).
Proof: transport the given square through F followed by V. Naturality for e is
its second square. The square gluing identity then inserts the ordinary source,
target and target-isomorphism maps. Functoriality of the single functor writes
the two endpoint composites as the displayed single maps. -/
theorem finiteBoundary_exact_glue
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    [Abelian A] [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory A] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (V : D ⥤ H) (G : A ⥤ C) (E : A ⥤ H)
    [F.Additive] [V.Additive] [G.Additive] [E.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : G ⋙ F ⋙ V ≅ E) {X Y : C} {X' Y' : A} {I Z W : H}
    (p : I ⟶ (F ⋙ V).obj X) (q : X ⟶ G.obj X') (r : Y ⟶ G.obj Y')
    (s : (F ⋙ V).obj Y ≅ Z) (t : E.obj Y' ⟶ W)
    (a : (DerivedCategory.singleFunctor A 0).obj X' ⟶
      ((DerivedCategory.singleFunctor A 0).obj Y')⟦(2 : ℤ)⟧)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (hc : (DerivedCategory.singleFunctor C 0).map q ≫ mapSingleArrow G (2 : ℤ) a =
      f ≫ ((DerivedCategory.singleFunctor C 0).map r)⟦(2 : ℤ)⟧') :
    (DerivedCategory.singleFunctor H 0).map (p ≫ (F ⋙ V).map q ≫ e.hom.app X') ≫
        (mapSingleArrow E (2 : ℤ) a ≫
          ((DerivedCategory.singleFunctor H 0).map t)⟦(2 : ℤ)⟧') =
      ((DerivedCategory.singleFunctor H 0).map p ≫ mapSingleArrow (F ⋙ V) (2 : ℤ) f ≫
          ((DerivedCategory.singleFunctor H 0).map s.hom)⟦(2 : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor H 0).map
          (s.inv ≫ (F ⋙ V).map r ≫ e.hom.app Y' ≫ t))⟦(2 : ℤ)⟧' := by
  let S := DerivedCategory.singleFunctor H 0
  have h := congrArg (fun b : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj (G.obj Y'))⟦(2 : ℤ)⟧ ↦
        mapSingleArrow (F ⋙ V) (2 : ℤ) b) hc
  rw [mapSingleArrow_precompose, mapSingleArrow_postcompose,
    mapSingleArrow_composite] at h
  have hn := mapSingleArrow_natIso (G ⋙ F ⋙ V) E e (2 : ℤ) a
  have hg := finiteBoundary_square_glue (2 : ℤ) (S.map p) (S.map ((F ⋙ V).map q))
    (S.map ((F ⋙ V).map r)) (S.map (e.hom.app X')) (S.map (e.hom.app Y')) (S.map t)
    (S.mapIso s) (mapSingleArrow E (2 : ℤ) a)
    (mapSingleArrow (G ⋙ F ⋙ V) (2 : ℤ) a) (mapSingleArrow (F ⋙ V) (2 : ℤ) f) h hn
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc] using hg
/-- Transfer a commuting square along four identified arrows.
Source: equality elimination (blueprint: lem-sfb-exact-arrow-transport). -/
theorem finiteBoundary_congr {D : Type*} [Category D] {X X' Y Y' : D}
    {q q' : X ⟶ X'} {r r' : Y ⟶ Y'} {a a' : X' ⟶ Y'} {b b' : X ⟶ Y}
    (hq : q = q') (hr : r = r') (ha : a = a') (hb : b = b')
    (h : q' ≫ a' = b' ≫ r') : q ≫ a = b ≫ r := by
  subst q'
  subst r'
  subst a'
  subst b'
  exact h
/-- Assemble an exact scalar square with its ordinary endpoint identifications.
Source: exact square gluing and equality elimination
(blueprint: lem-sfb-exact-arrow-transport).
Proof: use the exact transport square, apply the single functor to the source
and target equalities, and substitute the given evaluations of the two arrows. -/
theorem finiteBoundary_identified_glue
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    [Abelian A] [Abelian C] [Abelian D] [Abelian H]
    [HasDerivedCategory A] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory H]
    (F : C ⥤ D) (V : D ⥤ H) (G : A ⥤ C) (E : A ⥤ H)
    [F.Additive] [V.Additive] [G.Additive] [E.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : G ⋙ F ⋙ V ≅ E) {X Y : C} {X' Y' : A} {I Z W : H}
    (p : I ⟶ (F ⋙ V).obj X) (q : X ⟶ G.obj X') (r : Y ⟶ G.obj Y')
    (s : (F ⋙ V).obj Y ≅ Z) (t : E.obj Y' ⟶ W)
    (a : (DerivedCategory.singleFunctor A 0).obj X' ⟶
      ((DerivedCategory.singleFunctor A 0).obj Y')⟦(2 : ℤ)⟧)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (hc : (DerivedCategory.singleFunctor C 0).map q ≫ mapSingleArrow G (2 : ℤ) a =
      f ≫ ((DerivedCategory.singleFunctor C 0).map r)⟦(2 : ℤ)⟧')
    (q₀ : I ⟶ E.obj X') (r₀ : Z ⟶ W)
    (a₀ : (DerivedCategory.singleFunctor H 0).obj (E.obj X') ⟶
      ((DerivedCategory.singleFunctor H 0).obj W)⟦(2 : ℤ)⟧)
    (b₀ : (DerivedCategory.singleFunctor H 0).obj I ⟶
      ((DerivedCategory.singleFunctor H 0).obj Z)⟦(2 : ℤ)⟧)
    (hq : p ≫ (F ⋙ V).map q ≫ e.hom.app X' = q₀)
    (hr : s.inv ≫ (F ⋙ V).map r ≫ e.hom.app Y' ≫ t = r₀)
    (ha : a₀ = mapSingleArrow E (2 : ℤ) a ≫
      ((DerivedCategory.singleFunctor H 0).map t)⟦(2 : ℤ)⟧')
    (hb : b₀ = (DerivedCategory.singleFunctor H 0).map p ≫
      mapSingleArrow (F ⋙ V) (2 : ℤ) f ≫
      ((DerivedCategory.singleFunctor H 0).map s.hom)⟦(2 : ℤ)⟧') :
    (DerivedCategory.singleFunctor H 0).map q₀ ≫ a₀ =
      b₀ ≫ ((DerivedCategory.singleFunctor H 0).map r₀)⟦(2 : ℤ)⟧' := by
  let S := DerivedCategory.singleFunctor H 0
  exact finiteBoundary_congr (congrArg S.map hq.symm)
    (congrArg (fun r ↦ (S.map r)⟦(2 : ℤ)⟧') hr.symm) ha hb
    (finiteBoundary_exact_glue F V G E e p q r s t a f hc)
end AlgebraicGeometry.ProEtale.SpTowerClasses
