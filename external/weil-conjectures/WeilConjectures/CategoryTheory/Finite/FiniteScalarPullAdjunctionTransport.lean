/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Transport of an adjunction square through scalar and geometric presentations -/

@[expose] public section
set_option autoImplicit false
namespace CategoryTheory

private theorem uniqueness_transpose
    {A B : Type*} [Category A] [Category B]
    {F H : A ⥤ B} {R U : B ⥤ A} (a : F ⊣ R) (b : H ⊣ U) (d : R ≅ U) (M : A) :
    a.homEquiv M _ (((a.ofNatIsoRight d).leftAdjointUniq b).hom.app M) =
      b.unit.app M ≫ d.inv.app (H.obj M) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight d) b M
  erw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono (d.hom.app _)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact h

/-- Canonical scalar and geometric adjunction comparisons commute.
Source: the mates correspondence, Stacks Tag 06YY
(blueprint: lem-sf-finite-scalar-pull-adjunction-transport).
Proof: apply the composite Hom equivalence. The right square defining the first
comparison moves through naturality, the scalar unit transfers by left-adjoint
uniqueness, and the geometric unit transfers through the right comparison.
Both transposes are the same composite scalar and geometric unit. -/
theorem adjunctionSquareTransport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {S S' : B ⥤ D} {RX : D ⥤ B}
    {T T' : A ⥤ C} {RY : C ⥤ A} {G V : C ⥤ D} {U U' : D ⥤ C}
    (a : F ⊣ R) (s : S ⊣ RX) (s' : S' ⊣ RX) (t : T ⊣ RY) (t' : T' ⊣ RY)
    (g : G ⊣ U) (v : V ⊣ U') (d : U ⋙ RY ≅ RX ⋙ R) (e : U ≅ U') (M : A) :
    let δ := Functor.isoWhiskerRight e.symm RY ≪≫ d
    let q := ((a.comp s).ofNatIsoRight d.symm).leftAdjointUniq (t.comp g)
    let ν := ((a.comp s').ofNatIsoRight δ.symm).leftAdjointUniq (t'.comp v)
    let αx := s.leftAdjointUniq s'
    let αy := t.leftAdjointUniq t'
    let β := (g.ofNatIsoRight e).leftAdjointUniq v
    q.hom.app M ≫ G.map (αy.hom.app M) ≫ β.hom.app (T'.obj M) =
      αx.hom.app (F.obj M) ≫ ν.hom.app M := by
  let δ := Functor.isoWhiskerRight e.symm RY ≪≫ d
  let q := ((a.comp s).ofNatIsoRight d.symm).leftAdjointUniq (t.comp g)
  let ν := ((a.comp s').ofNatIsoRight δ.symm).leftAdjointUniq (t'.comp v)
  let αx := s.leftAdjointUniq s'
  let αy := t.leftAdjointUniq t'
  let β := (g.ofNatIsoRight e).leftAdjointUniq v
  have hq : (a.comp s).homEquiv M _ (q.hom.app M) =
      (t.comp g).unit.app M ≫ d.hom.app (G.obj (T.obj M)) :=
    uniqueness_transpose (a.comp s) (t.comp g) d.symm M
  have hν : (a.comp s').homEquiv M _ (ν.hom.app M) =
      (t'.comp v).unit.app M ≫ δ.hom.app (V.obj (T'.obj M)) :=
    uniqueness_transpose (a.comp s') (t'.comp v) δ.symm M
  have hβ : g.unit.app (T'.obj M) ≫ U.map (β.hom.app (T'.obj M)) =
      v.unit.app (T'.obj M) ≫ e.inv.app (V.obj (T'.obj M)) := by
    exact uniqueness_transpose g v e (T'.obj M)
  apply ((a.comp s).homEquiv M _).injective
  have hrhs : (a.comp s).homEquiv M _
      (αx.hom.app (F.obj M) ≫ ν.hom.app M) =
        (t'.comp v).unit.app M ≫ δ.hom.app (V.obj (T'.obj M)) := by
    erw [Adjunction.comp_homEquiv]
    change a.homEquiv M _
      (s.homEquiv _ _ ((s.leftAdjointUniq s').hom.app _ ≫ ν.hom.app M)) = _
    erw [leftAdjointUniq_homEquiv_comp]
    erw [Adjunction.comp_homEquiv] at hν
    exact hν
  dsimp only [Functor.comp_obj] at hrhs hq ⊢
  erw [hrhs]
  erw [(a.comp s).homEquiv_naturality_right, hq]
  have hd := d.hom.naturality (G.map (αy.hom.app M) ≫ β.hom.app (T'.obj M))
  dsimp only [Functor.comp_map] at hd
  erw [Category.assoc, ← hd, Adjunction.comp_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  have hu := g.unit.naturality (αy.hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  erw [← RY.map_comp_assoc, ← hu]
  simp only [RY.map_comp, Category.assoc]
  erw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  erw [Category.assoc, ← RY.map_comp_assoc, hβ]
  simp only [Functor.map_comp, Category.assoc]
  simp [δ, Category.assoc]

end CategoryTheory
