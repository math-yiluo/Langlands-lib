/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkReverseComponentsLift
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkChainMapEquality

/-! # Spreading a single stalk homotopy of a strictly perfect complex

Source: Stacks Project, Tags 09RE, 0BC7 (2) and 01CP.
(blueprint: lem-sc-perfect-open-stalk-homotopy-spread).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private def homotopy_of_natIso
    {A C : Type*} [Category A] [Category C] [Preadditive C]
    {F G : A ⥤ CochainComplex C ℤ} (e : F ≅ G)
    {K L : A} (f g : K ⟶ L) (h : Homotopy (G.map f) (G.map g)) :
    Homotopy (F.map f) (F.map g) := by
  have H := (h.compLeft (e.hom.app K)).compRight (e.inv.app L)
  simpa only [Category.assoc, ← e.hom.naturality_assoc,
    e.hom_inv_id_app, Category.comp_id] using H

private def restriction_comp_iso (X : Scheme.{u}) (V Z W : X.Opens)
    (hZV : Z ≤ V) (hWZ : W ≤ Z) :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hZV)) ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWZ)) ≅
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hWZ.trans hZV)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
-- Nested restriction and stalk comparisons require extra definitional-equality checks.
/-- Two fixed endomorphisms which are homotopic at the stalk become homotopic
on an affine neighbourhood inside any prescribed smaller neighbourhood.
Source: Stacks Project, Tag 09RE, affine case (1); Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-homotopy-spread).

Proof: Lift the reverse-degree components, without equations, inside T. The
canonical stalk comparison identifies the stalk of their null-homotopic map with
the null-homotopic map of the given stalk components. The input homotopy identifies
this with the difference a-b. Shrink until these two chain maps agree, using
bounded finite-retract stalk equality. Apply the canonical null homotopy and the
subtraction equivalence to obtain a homotopy between a and b. Finally choose an
affine subneighbourhood and restrict the homotopy there. Iterated slice restriction
is definitionally identified with direct restriction. -/
theorem exists_affine_perfect_open_stalk_homotopy_spread
    (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (x : X) (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
    (a b : (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P))
    (hab : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map a)
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map b)))
    (T : X.Opens) (hTV : T ≤ V) (hxT : x ∈ T) :
    ∃ (W : X.Opens) (hWT : W ≤ T), x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (Homotopy
        (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (hWT.trans hTV))).mapHomologicalComplex (.up ℤ)).map a)
        (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE (hWT.trans hTV))).mapHomologicalComplex (.up ℤ)).map b)) := by
  obtain ⟨h⟩ := hab
  obtain ⟨Z, hZT, hxZ, e, k, hkzero, hklift⟩ :=
    exists_perfect_open_stalk_reverse_components_lift
      X U P hP x V hxV hVU T hTV hxT h.hom h.zero
  let PV := ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P
  let R₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE (hZT.trans hTV))
  let R := R₀.mapHomologicalComplex (.up ℤ)
  let S₀ := openModuleStalkFunctor X Z ⟨x, hxZ⟩
  let S := S₀.mapHomologicalComplex (.up ℤ)
  let F := (openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)
  have hnull : S.map (Homotopy.nullHomotopicMap k) =
      (e.app PV).hom ≫ Homotopy.nullHomotopicMap h.hom ≫ (e.app PV).inv := by
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
          (e.app PV).hom ≫ F.map (a - b) := e.hom.naturality (a - b)
      _ = _ := by
        congr 1
        rw [Functor.map_sub]
        ext n : 1
        change (F.map a).f n - (F.map b).f n = _
        apply sub_eq_iff_eq_add.mpr
        exact h.comm n
  obtain ⟨W, hWZ, hxW, heq⟩ := exists_perfect_open_stalk_chain_map_eq
    X U P hP x V Z hxZ hVU (hZT.trans hTV)
      (R.map (a - b)) (Homotopy.nullHomotopicMap k) hstalk
  let A₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)
  let A := A₀.mapHomologicalComplex (.up ℤ)
  have hzero : Homotopy (A.map (R.map (a - b))) 0 := by
    rw [heq]
    simpa only [Functor.map_zero] using A₀.mapHomotopy (Homotopy.nullHomotopy k hkzero)
  have hW : Homotopy (A.map (R.map a)) (A.map (R.map b)) :=
    Homotopy.equivSubZero.symm (by simpa only [Functor.map_sub] using hzero)
  let c := Functor.mapHomologicalComplexCompIso
    (restriction_comp_iso X V Z W (hZT.trans hTV) hWZ) (.up ℤ)
  have hW' := homotopy_of_natIso c.symm a b hW
  obtain ⟨B, hB, hxB, hBW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let d := Functor.mapHomologicalComplexCompIso
    (restriction_comp_iso X V W B (hWZ.trans (hZT.trans hTV)) hBW) (.up ℤ)
  have hB' := (SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE hBW)).mapHomotopy hW'
  exact ⟨B, (hBW.trans hWZ).trans hZT, hxB, hB,
    ⟨homotopy_of_natIso d.symm a b hB'⟩⟩

end
end AlgebraicGeometry.Scheme
