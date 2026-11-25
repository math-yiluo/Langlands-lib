/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact single-arrow calculus

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-exact-arrow-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃ t₄ t₅
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses.FiniteExactArrow


/-- Compatibility of exact derived arrows with the indicated functor operation.
Source: exact functors on Ext and their canonical single/shift comparisons
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_ext
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {n : ℕ} (x : Ext.{w₁} X Y n) :
    mapSingleArrow F (n : ℤ) x.hom = (x.mapExactFunctor F).hom := by
  simpa only [mapSingleArrow, ShiftedHom.map, Category.assoc] using
    (Ext.mapExactFunctor_hom F x).symm

/-- Compatibility of exact derived arrows with the indicated functor operation.
Source: exact functors on Ext and their canonical single/shift comparisons
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_comp_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} H]
    [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} H] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : C ⥤ H) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (τ : K ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w₁} X Y n) :
    mapSingleArrow G (n : ℤ) (mapSingleArrow F (n : ℤ) x.hom) =
      (DerivedCategory.singleFunctor H 0).map (τ.inv.app X) ≫
        mapSingleArrow K (n : ℤ) x.hom ≫
        ((DerivedCategory.singleFunctor H 0).map (τ.hom.app Y))⟦(n : ℤ)⟧' := by
  have h := congrArg (fun y : Ext.{w₃} (G.obj (F.obj X)) (G.obj (F.obj Y)) n ↦
    (show (DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj X)) ⟶
      ((DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj Y)))⟦(n : ℤ)⟧ from y.hom))
    (Ext.mapExactFunctor_mapExactFunctor_of_iso F G K τ x)
  simp only [Ext.mapExactFunctor_hom, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc] at h
  simpa only [mapSingleArrow, Category.assoc] using h

/-- Composite exact transport of an arbitrary derived arrow, using only Ext in
its source category. Source: exact functors and the Ext realization equivalence
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_comp_iso_arrow
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} H]
    [HasExt.{w₁} C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : C ⥤ H) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (τ : K ≅ F ⋙ G) {X Y : C} (n : ℕ)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    mapSingleArrow G (n : ℤ) (mapSingleArrow F (n : ℤ) a) =
      (DerivedCategory.singleFunctor H 0).map (τ.inv.app X) ≫
        mapSingleArrow K (n : ℤ) a ≫
        ((DerivedCategory.singleFunctor H 0).map (τ.hom.app Y))⟦(n : ℤ)⟧' := by
  have : HasExt.{t₂} D := hasExt_of_hasDerivedCategory D
  have : HasExt.{t₃} H := hasExt_of_hasDerivedCategory H
  obtain ⟨x, hx⟩ := (Ext.homEquiv (X := X) (Y := Y) (n := n)).surjective a
  change x.hom = a at hx
  subst a
  exact mapSingleArrow_comp_iso F G K τ x

/-- Successive exact transport is transport by the composite functor.
Source: exact composition with its identity natural isomorphism
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_comp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} H]
    [HasExt.{w₁} C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} (n : ℕ)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    mapSingleArrow G (n : ℤ) (mapSingleArrow F (n : ℤ) a) =
      mapSingleArrow (F ⋙ G) (n : ℤ) a := by
  have h := mapSingleArrow_comp_iso_arrow F G (F ⋙ G) (Iso.refl _) n a
  simpa only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h

/-- Three successive exact transports commute with an isomorphic alternate pair.
Source: composition of exact functors and naturality under a functor isomorphism
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_three_comp_iso_arrow
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    {I : Type u₂} [Category.{v₂} I] [Abelian I]
    {B : Type u₃} [Category.{v₃} B] [Abelian B]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} H]
    [HasDerivedCategory.{t₄} I] [HasDerivedCategory.{t₅} B]
    [HasExt.{w₁} C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : H ⥤ B) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (U : C ⥤ I) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : I ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (τ : U ⋙ V ≅ (F ⋙ G) ⋙ K) {X Y : C} (n : ℕ)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    mapSingleArrow K (n : ℤ) (mapSingleArrow G (n : ℤ) (mapSingleArrow F (n : ℤ) a)) =
      (DerivedCategory.singleFunctor B 0).map (τ.inv.app X) ≫
        mapSingleArrow V (n : ℤ) (mapSingleArrow U (n : ℤ) a) ≫
        ((DerivedCategory.singleFunctor B 0).map (τ.hom.app Y))⟦(n : ℤ)⟧' := by
  have h := mapSingleArrow_comp_iso_arrow (F ⋙ G) K (U ⋙ V) τ n a
  rw [← mapSingleArrow_comp F G, ← mapSingleArrow_comp U V] at h
  exact h

/-- Compatibility of exact derived arrows with the indicated functor operation.
Source: exact functors on Ext and their canonical single/shift comparisons
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_precomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X X' Y : C} (a : X' ⟶ X) (n : ℤ)
    (h : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow F n ((DerivedCategory.singleFunctor C 0).map a ≫ h) =
      (DerivedCategory.singleFunctor D 0).map (F.map a) ≫ mapSingleArrow F n h := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

/-- Compatibility of exact derived arrows with the indicated functor operation.
Source: exact functors on Ext and their canonical single/shift comparisons
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_postcomp
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y Y' : C} (b : Y ⟶ Y') (n : ℤ)
    (h : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow F n (h ≫ ((DerivedCategory.singleFunctor C 0).map b)⟦n⟧') =
      mapSingleArrow F n h ≫
        ((DerivedCategory.singleFunctor D 0).map (F.map b))⟦n⟧' := by
  simp only [mapSingleArrow, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]
  have hn := (F.mapDerivedCategorySingleFunctor 0).hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [← Functor.map_comp, hn, Functor.map_comp]

/-- The canonical single comparisons for a composite exact functor give successive
single-arrow transport. Source: exact single and shift functoriality
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem coordinate_composite
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {H : Type u₃} [Category.{v₃} H] [Abelian H]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D] [HasDerivedCategory.{t₃} H]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ H) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {X' Y' : H}
    (SX : (F.mapDerivedCategory ⋙ G.mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj X)))
    (SY : (F.mapDerivedCategory ⋙ G.mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor C 0).obj Y) ≅
      (DerivedCategory.singleFunctor H 0).obj (G.obj (F.obj Y)))
    (hx : SX = G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app X) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj X))
    (hy : SY = G.mapDerivedCategory.mapIso ((F.mapDerivedCategorySingleFunctor 0).app Y) ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (F.obj Y))
    (u : G.obj (F.obj X) ≅ X') (v : G.obj (F.obj Y) ≅ Y') (n : ℤ)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    (((DerivedCategory.singleFunctor H 0).mapIso u).symm ≪≫ SX.symm).hom ≫
        G.mapDerivedCategory.map (F.mapDerivedCategory.map a) ≫
        (((F.mapDerivedCategory ⋙ G.mapDerivedCategory).commShiftIso n).app _ ≪≫
          (shiftFunctor _ n).mapIso
            (SY ≪≫ (DerivedCategory.singleFunctor H 0).mapIso v)).hom =
      (DerivedCategory.singleFunctor H 0).map u.inv ≫
        mapSingleArrow G n (mapSingleArrow F n a) ≫
        ((DerivedCategory.singleFunctor H 0).map v.hom)⟦n⟧' := by
  rw [hx, hy]
  simp only [mapSingleArrow, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Functor.commShiftIso_comp_hom_app, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]

/-- Exact Yoneda composition and its realization respect the indicated boundary map.
Source: naturality of short-exact extension classes and exact functors on Ext
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem kummerComposite_ext
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{t₁} C] [HasExt.{w₁} C]
    {s : ShortComplex C} (hs : s.ShortExact) {X : C} (x : Ext.{w₁} X s.X₃ 1) :
    kummerComposite s hs x.hom = (x.comp hs.extClass rfl).hom := by
  simp only [kummerComposite, Ext.comp_hom, ShortComplex.ShortExact.extClass_hom,
    ShiftedHom.comp, Int.natCast_one, Int.natCast_add, shiftFunctorAdd'_eq_shiftFunctorAdd]

/-- Exact Yoneda composition and its realization respect the indicated boundary map.
Source: naturality of short-exact extension classes and exact functors on Ext
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapped_composite_boundary
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {s : ShortComplex C} {t : ShortComplex D} (hs : s.ShortExact) (ht : t.ShortExact)
    (ψ : s.map F ⟶ t) {X : C} {X' : D} (a : X' ⟶ F.obj X)
    (x : Ext.{w₁} X s.X₃ 1) :
    ((Ext.mk₀ a).comp
      ((x.mapExactFunctor F).comp (Ext.mk₀ ψ.τ₃) (add_zero 1)) (zero_add 1)).comp
        ht.extClass (rfl : 1 + 1 = 2) =
      (Ext.mk₀ a).comp
        (((x.comp hs.extClass (rfl : 1 + 1 = 2)).mapExactFunctor F).comp
          (Ext.mk₀ ψ.τ₁) (add_zero 2)) (zero_add 2) := by
  have hn := ShortComplex.ShortExact.extClass_naturality (hs.map_of_exact F) ht ψ
  rw [← Ext.mapExactFunctor_extClass] at hn
  rotate_left
  · exact hs
  rw [Ext.comp_assoc (Ext.mk₀ a)
    ((x.mapExactFunctor F).comp (Ext.mk₀ ψ.τ₃) (add_zero 1)) ht.extClass
      (zero_add 1) rfl (zero_add 2)]
  rw [Ext.comp_assoc_of_second_deg_zero, ← hn, Ext.mapExactFunctor_comp]
  rw [Ext.comp_assoc_of_third_deg_zero]

/-- Exact Yoneda composition and its realization respect the indicated boundary map.
Source: naturality of short-exact extension classes and exact functors on Ext
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapped_kummer_composite
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {s : ShortComplex C} (hs : s.ShortExact) {X : C} (x : Ext.{w₁} X s.X₃ 1) :
    mapSingleArrow F (2 : ℤ) (kummerComposite s hs x.hom) =
      ((x.mapExactFunctor F).comp (hs.map_of_exact F).extClass (rfl : 1 + 1 = 2)).hom := by
  have h := mapSingleArrow_ext F (x.comp hs.extClass (rfl : 1 + 1 = 2))
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass] at h
  exact (congrArg (mapSingleArrow F (2 : ℤ)) (kummerComposite_ext hs x)).trans h

section
attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

/-- Exact evaluation cancels constant-system transport of any single arrow.
Source: functoriality of Ext and the identity of evaluation on constant systems
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_eval_const
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {I : Type u₂} [Category.{v₂} I] [Abelian (I ⥤ C)]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} (I ⥤ C)]
    [HasExt.{w₁} C] [EnoughInjectives C] [(Functor.const I (C := C)).Additive]
    {X Y : C} (i : I) [((evaluation I C).obj i).Additive] (m : ℕ)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(m : ℤ)⟧) :
    mapSingleArrow ((evaluation I C).obj i) (m : ℤ)
      (mapSingleArrow (Functor.const I) (m : ℤ) a) = a := by
  have : HasExt.{t₂} (I ⥤ C) := hasExt_of_hasDerivedCategory _
  obtain ⟨x, hx⟩ := (Ext.homEquiv (X := X) (Y := Y) (n := m)).surjective a
  change x.hom = a at hx
  subst a
  rw [mapSingleArrow_ext (Functor.const I) x,
    mapSingleArrow_ext ((evaluation I C).obj i)]
  have h := Ext.mapExactFunctor_mapExactFunctor_of_iso (Functor.const I)
    ((evaluation I C).obj i) (𝟭 C) (Iso.refl _) x
  simp only [Ext.mapExactFunctor_id, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app] at h
  apply congrArg (fun e : Ext.{w₁} X Y m ↦ e.hom)
  exact h.trans (by
    change (Ext.mk₀ (𝟙 _)).comp (x.comp (Ext.mk₀ (𝟙 _)) (add_zero m))
      (zero_add m) = x
    rw [Ext.mk₀_id_comp, Ext.comp_mk₀_id])

end

/-- Exact functors preserve the degree-two Kummer connecting composite.
Source: naturality of extension classes under exact functors
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem mapSingleArrow_kummerComposite
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{w₁} C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {s : ShortComplex C} (hs : s.ShortExact) {X : C}
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj s.X₃)⟦(1 : ℤ)⟧) :
    mapSingleArrow F (2 : ℤ) (kummerComposite s hs a) =
      kummerComposite (s.map F) (hs.map_of_exact F) (mapSingleArrow F (1 : ℤ) a) := by
  have : HasExt.{t₂} D := hasExt_of_hasDerivedCategory D
  obtain ⟨x, hx⟩ := (Ext.homEquiv (X := X) (Y := s.X₃) (n := 1)).surjective a
  change x.hom = a at hx
  subst a
  have hx : mapSingleArrow F (1 : ℤ) x.hom = (x.mapExactFunctor F).hom :=
    mapSingleArrow_ext F x
  rw [hx]
  have hr : kummerComposite (s.map F) (hs.map_of_exact F) (x.mapExactFunctor F).hom =
      ((x.mapExactFunctor F).comp (hs.map_of_exact F).extClass (rfl : 1 + 1 = 2)).hom :=
    kummerComposite_ext (hs.map_of_exact F) (x.mapExactFunctor F)
  exact (mapped_kummer_composite F hs x).trans hr.symm

/-- A map of short exact sequences transports the Kummer boundary of an extension.
Source: short-exact extension naturality and Yoneda associativity
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem kummerComposite_comparison
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{w₁} C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {s : ShortComplex C} {t : ShortComplex D} (hs : s.ShortExact) (ht : t.ShortExact)
    (ψ : s.map F ⟶ t) {X : C} {X' : D} (a : X' ⟶ F.obj X)
    (x : Ext.{w₁} X s.X₃ 1) :
    kummerComposite t ht
      ((DerivedCategory.singleFunctor D 0).map a ≫
        mapSingleArrow F (1 : ℤ) x.hom ≫
        ((DerivedCategory.singleFunctor D 0).map ψ.τ₃)⟦(1 : ℤ)⟧') =
      (DerivedCategory.singleFunctor D 0).map a ≫
        mapSingleArrow F (2 : ℤ) (x.comp hs.extClass (rfl : 1 + 1 = 2)).hom ≫
        ((DerivedCategory.singleFunctor D 0).map ψ.τ₁)⟦(2 : ℤ)⟧' := by
  have : HasExt.{t₂} D := hasExt_of_hasDerivedCategory D
  let γ := (Ext.mk₀ a).comp
    ((x.mapExactFunctor F).comp (Ext.mk₀ ψ.τ₃) (add_zero 1)) (zero_add 1)
  have hc := kummerComposite_ext ht γ
  have he := congrArg (fun y ↦ y.hom) (mapped_composite_boundary F hs ht ψ a x)
  simp only [γ, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, ← mapSingleArrow_ext] at hc he
  convert hc.trans he using 1
  simp only [Ext.comp_hom]
  rfl

/-- A source normalization cancels the inverse comparison of a transported arrow.
Source: exact single-arrow endpoint naturality and inverse cancellation
(blueprint: lem-sfb-finite-exact-arrow-calculus). -/
theorem coordinate_transport_of_comparison
    {H : Type u₁} [Category.{v₁} H] [Abelian H]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{t₁} H] [HasDerivedCategory.{t₂} B]
    (K : H ⥤ B) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {X Y X' Y' : H} {X₀ Y₀ Z Z' : B}
    (u : X ≅ X') (v : Y ≅ Y') (α : X₀ ≅ K.obj X) (β : Y₀ ≅ K.obj Y)
    (q : Z' ⟶ K.obj X') (i : Z' ⟶ Z) (e : Z ⟶ X₀)
    (hq : q = i ≫ e ≫ α.hom ≫ K.map u.hom) (m : ℤ)
    (a : (DerivedCategory.singleFunctor H 0).obj X ⟶
      ((DerivedCategory.singleFunctor H 0).obj Y)⟦m⟧)
    (d : (DerivedCategory.singleFunctor B 0).obj X₀ ⟶
      ((DerivedCategory.singleFunctor B 0).obj Y₀)⟦m⟧)
    (hd : mapSingleArrow K m a =
      (DerivedCategory.singleFunctor B 0).map α.inv ≫ d ≫
        ((DerivedCategory.singleFunctor B 0).map β.hom)⟦m⟧')
    (a' : (DerivedCategory.singleFunctor H 0).obj X' ⟶
      ((DerivedCategory.singleFunctor H 0).obj Y')⟦m⟧)
    (ha' : a' = (DerivedCategory.singleFunctor H 0).map u.inv ≫ a ≫
      ((DerivedCategory.singleFunctor H 0).map v.hom)⟦m⟧')
    (r : Y₀ ⟶ K.obj Y') (hr : r = β.hom ≫ K.map v.hom) :
    (DerivedCategory.singleFunctor B 0).map q ≫ mapSingleArrow K m a' =
      (DerivedCategory.singleFunctor B 0).map i ≫
        (DerivedCategory.singleFunctor B 0).map e ≫ d ≫
        ((DerivedCategory.singleFunctor B 0).map r)⟦m⟧' := by
  rw [hr, ha', mapSingleArrow_precomp, mapSingleArrow_postcomp, hd, hq]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (DerivedCategory.singleFunctor B 0)
    (K.map u.hom) (K.map u.inv), ← K.map_comp, u.hom_inv_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc (DerivedCategory.singleFunctor B 0)
    α.hom α.inv, α.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.SpTowerClasses.FiniteExactArrow
