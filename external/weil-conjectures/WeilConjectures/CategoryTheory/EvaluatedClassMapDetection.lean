/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Detection of evaluated ordinary maps in class coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory

@[reassoc] private theorem evaluated_single_naturality
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {M N : A} (f : M ⟶ N) :
    V.mapDerivedCategory.map (((DerivedCategory.singleFunctor A 0).map f)⟦(2 : ℤ)⟧') ≫
        (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj N) ≫
        (((V.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(2 : ℤ)⟧') =
      (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
        (((V.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(2 : ℤ)⟧') ≫
        (((DerivedCategory.singleFunctor B 0).map (V.map f))⟦(2 : ℤ)⟧') := by
  rw [Functor.commShiftIso_hom_naturality_assoc]
  congr 1
  have hn := (V.mapDerivedCategorySingleFunctor 0).hom.naturality f
  simpa only [Functor.comp_map, Functor.map_comp] using
    congrArg (fun z ↦ z⟦(2 : ℤ)⟧') hn

/-- Exact evaluation, an isomorphic pair of coordinates and class detection recover
ordinary maps from equality of the evaluated shifted composites.
Source: diagonal coefficient changes (3), exact evaluation and single comparisons.
(blueprint: lem-diagonal-evaluated-class-map-detection).

Proof: naturality of the shift and exact-single comparisons moves evaluation of
single(a) and single(b) to single(V(a)) and single(V(b)). Postcompose both by the
coordinate isomorphism v. Conjugate V(a) and V(b) by t and v. The normalized class
equation and injectivity of postcomposition by c identify these conjugates, since
s is an isomorphism. Cancel t inverse and v to recover V(a) = V(b). -/
theorem Functor.detect_evaluated_single_maps
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {X : DerivedCategory A} {M N : A} {P Q : B}
    (z : X ⟶ ((DerivedCategory.singleFunctor A 0).obj M)⟦(2 : ℤ)⟧)
    (s : V.mapDerivedCategory.obj X ≅ (DerivedCategory.singleFunctor B 0).obj P)
    (t : V.obj M ≅ Q) (v : V.obj N ≅ Q)
    (c : (DerivedCategory.singleFunctor B 0).obj P ⟶
      ((DerivedCategory.singleFunctor B 0).obj Q)⟦(2 : ℤ)⟧)
    (ht : V.mapDerivedCategory.map z ≫
        (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
        (((V.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(2 : ℤ)⟧') ≫
        (((DerivedCategory.singleFunctor B 0).map t.hom)⟦(2 : ℤ)⟧') = s.hom ≫ c)
    (hc : Function.Injective (fun f : Q ⟶ Q ↦ c ≫
      (((DerivedCategory.singleFunctor B 0).map f)⟦(2 : ℤ)⟧')))
    (a b : M ⟶ N)
    (heq : V.mapDerivedCategory.map
        (z ≫ (((DerivedCategory.singleFunctor A 0).map a)⟦(2 : ℤ)⟧')) =
      V.mapDerivedCategory.map
        (z ≫ (((DerivedCategory.singleFunctor A 0).map b)⟦(2 : ℤ)⟧'))) :
    V.map a = V.map b := by
  have hn := congrArg (fun f ↦ f ≫
    (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor A 0).obj N) ≫
    (((V.mapDerivedCategorySingleFunctor 0).hom.app N)⟦(2 : ℤ)⟧') ≫
    (((DerivedCategory.singleFunctor B 0).map v.hom)⟦(2 : ℤ)⟧')) heq
  simp only [Functor.map_comp, Category.assoc] at hn
  rw [evaluated_single_naturality_assoc, evaluated_single_naturality_assoc] at hn
  let J := DerivedCategory.singleFunctor B 0 ⋙ shiftFunctor (DerivedCategory B) (2 : ℤ)
  let z' := V.mapDerivedCategory.map z ≫
    (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor A 0).obj M) ≫
    (((V.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(2 : ℤ)⟧')
  have ht' : z' ≫ J.map t.hom = s.hom ≫ c := by
    simpa only [z', J, Functor.comp_map, Category.assoc] using ht
  have hn' : z' ≫ J.map (V.map a) ≫ J.map v.hom =
      z' ≫ J.map (V.map b) ≫ J.map v.hom := by
    simpa only [z', J, Functor.comp_map, Category.assoc] using hn
  have hc' : Function.Injective (fun f : Q ⟶ Q ↦ c ≫ J.map f) := hc
  have collapse (a : M ⟶ N) :
      s.hom ≫ c ≫ J.map (t.inv ≫ V.map a ≫ v.hom) =
        z' ≫ J.map (V.map a) ≫ J.map v.hom := by
    calc
      _ = (s.hom ≫ c) ≫ J.map (t.inv ≫ V.map a ≫ v.hom) := by
        simp only [Category.assoc]
      _ = (z' ≫ J.map t.hom) ≫ J.map (t.inv ≫ V.map a ≫ v.hom) := by
        rw [ht']
      _ = z' ≫ J.map (t.hom ≫ t.inv ≫ V.map a ≫ v.hom) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = _ := by
        simp only [Iso.hom_inv_id_assoc, Functor.map_comp]
  have hconj : t.inv ≫ V.map a ≫ v.hom = t.inv ≫ V.map b ≫ v.hom := by
    apply hc'
    apply (cancel_epi s.hom).1
    simpa only [Category.assoc, collapse] using hn'
  apply (cancel_epi t.inv).1
  apply (cancel_mono v.hom).1
  simpa only [Category.assoc] using hconj



end CategoryTheory
