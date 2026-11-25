/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteFreeReverseComponentsLift
import WeilConjectures.AlgebraicGeometry.FiniteFreeChainMapStalkEquality

/-! # Spreading a homotopy of a bounded finite free complex

Source: lemma-coherent-base-change-invertible-sheaves--3, extension of finite calculations near a
point. (blueprint: lem-pc-finite-free-stalk-homotopy-p-only)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private def homotopyOfNaturalIso
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    {F G : C ⥤ CochainComplex D ℤ} (e : F ≅ G)
    {X : C} (a b : X ⟶ X) (h : Homotopy (G.map a) (G.map b)) :
    Homotopy (F.map a) (F.map b) := by
  have ha : F.map a ≫ (e.app X).hom = (e.app X).hom ≫ G.map a := e.hom.naturality a
  have hb : F.map b ≫ (e.app X).hom = (e.app X).hom ≫ G.map b := e.hom.naturality b
  have ht := (h.compLeft (e.app X).hom).compRight (e.app X).inv
  rw [← ha, ← hb] at ht
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht

/-- A stalk homotopy of two fixed endomorphisms spreads near the point.

Source: blueprint sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus,
proof, extension of the finite calculation to a neighbourhood; expanded in
lem-pc-finite-free-stalk-homotopy-pair-shrink, steps 1--3.
(blueprint: lem-pc-finite-free-stalk-homotopy-p-only).

Proof: Choose the termwise finite bases supplied by hfree and a homotopy in hP.
Restriction and pullback carry these bases to finite bases; over Spec O_{Y,y}
the coefficients of its components are elements of O_{Y,y}. By hge and hle,
only the reverse-degree components with both degrees in [0,d] can be nonzero.
There are finitely many such components and finitely many entries in each.
Represent their entries by structure-sheaf sections on neighbourhoods of y
inside V, and intersect these neighbourhoods. Use the bases to make these
sections into sheaf-module morphisms, setting all other components to zero.
For each degree in [0,d], the matrix of a-dh-hd-b has zero germs because hP
is a homotopy of the specified maps. The germ equality criterion gives a
smaller neighbourhood where each entry is zero. Intersect the finitely many
neighbourhoods once more. The resulting components satisfy Homotopy.comm;
outside [0,d] the source terms are zero, so the equations hold automatically.
Only reverse-degree components were retained, so Homotopy.zero also holds.
This constructs the required homotopy after restriction. Rank zero and d=0
cause no difficulty: empty matrices or the empty list of reverse components
have no coefficients to lift, and only the fixed-map equations remain. -/
theorem exists_shrink_homotopy_P_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (a b : (((restrictFunctor V.ι).mapHomologicalComplex _).obj P) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P))
    (hP : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map a)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map b))) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map a)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map b)) := by
  classical
  obtain ⟨h⟩ := hP
  obtain ⟨U, hUV, hyU, e, k, hkzero, hklift⟩ :=
    exists_lift_reverse_components P d hge hle hfree y V hyV h.hom h.zero
  let PV := ((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let R := (restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex (ComplexShape.up ℤ)
  let S := (Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let T := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hnull : S.map (Homotopy.nullHomotopicMap k) =
      (e.app PV).hom ≫ Homotopy.nullHomotopicMap h.hom ≫ (e.app PV).inv := by
    set_option backward.isDefEq.respectTransparency false in
      rw [Homotopy.map_nullHomotopicMap, Homotopy.nullHomotopicMap_comp,
      Homotopy.comp_nullHomotopicMap]
    congr 1
    funext i j
    exact hklift i j
  have hstalk : S.map (R.map (a - b)) = S.map (Homotopy.nullHomotopicMap k) := by
    apply (cancel_mono (e.app PV).hom).1
    rw [hnull]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      S.map (R.map (a - b)) ≫ (e.app PV).hom =
          (e.app PV).hom ≫ T.map (a - b) := e.hom.naturality (a - b)
      _ = _ := by
        congr 1
        rw [Functor.map_sub]
        ext n : 1
        change (T.map a).f n - (T.map b).f n = _
        apply sub_eq_iff_eq_add.mpr
        exact h.comm n
  obtain ⟨W, hWU, hyW, heq⟩ := exists_shrink_chainMap_eq_of_stalk
    P d hge hle hfree y V U hUV hyU (R.map (a - b))
      (Homotopy.nullHomotopicMap k) hstalk
  let F := (restrictFunctor (Y.homOfLE hWU)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hzero : Homotopy (F.map (R.map (a - b))) 0 := by
    rw [heq]
    simpa only [Functor.map_zero] using
      (restrictFunctor (Y.homOfLE hWU)).mapHomotopy (Homotopy.nullHomotopy k hkzero)
  have hab : Homotopy (F.map (R.map a)) (F.map (R.map b)) :=
    Homotopy.equivSubZero.symm (by simpa only [Functor.map_sub] using hzero)
  have hcomp : Y.homOfLE hWU ≫ Y.homOfLE hUV = Y.homOfLE (hWU.trans hUV) := by
    apply (cancel_mono V.ι).1
    simp only [Category.assoc, Scheme.homOfLE_ι]
  let c := NatIso.mapHomologicalComplex ((restrictFunctorCongr hcomp).symm ≪≫
    restrictFunctorComp (Y.homOfLE hWU) (Y.homOfLE hUV)) (ComplexShape.up ℤ)
  refine ⟨W, hWU.trans hUV, hyW, ⟨?_⟩⟩
  exact homotopyOfNaturalIso c a b hab


end AlgebraicGeometry.Scheme.Modules
