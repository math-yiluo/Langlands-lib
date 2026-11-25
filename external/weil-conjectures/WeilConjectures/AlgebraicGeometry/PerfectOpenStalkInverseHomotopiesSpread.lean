/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkHomotopySpread
import WeilConjectures.AlgebraicGeometry.StalkInternalHomFinitePresentation

/-! # Spreading two inverse homotopies

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-open-stalk-inverse-homotopies-spread).
-/

@[expose] public section

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

private theorem inverse_homotopies_of_natIso
    {A C : Type*} [Category A] [Category C] [Preadditive C]
    {F G : A ⥤ CochainComplex C ℤ} (e : F ≅ G)
    {P Q : A} (f : P ⟶ Q) (g : G.obj Q ⟶ G.obj P)
    (hfg : Homotopy (G.map f ≫ g) (𝟙 _))
    (hgf : Homotopy (g ≫ G.map f) (𝟙 _)) :
    ∃ gF : F.obj Q ⟶ F.obj P,
      Nonempty (Homotopy (F.map f ≫ gF) (𝟙 _)) ∧
      Nonempty (Homotopy (gF ≫ F.map f) (𝟙 _)) := by
  let gF := e.hom.app Q ≫ g ≫ e.inv.app P
  refine ⟨gF, ⟨?_⟩, ⟨?_⟩⟩
  · have H := (hfg.compLeft (e.hom.app P)).compRight (e.inv.app P)
    simpa only [gF, Category.assoc, ← e.hom.naturality_assoc,
      Category.id_comp, Category.comp_id, e.hom_inv_id_app] using H
  · have H := (hgf.compLeft (e.hom.app Q)).compRight (e.inv.app Q)
    have heq : gF ≫ F.map f = e.hom.app Q ≫ (g ≫ G.map f) ≫ e.inv.app Q := by
      simp only [gF, Category.assoc]
      rw [← e.inv.naturality f]
    rw [heq]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id,
      e.hom_inv_id_app] using H

set_option backward.isDefEq.respectTransparency false in
-- Explicit comparisons avoid unfolding large iterated restriction complex objects.
/-- Two given inverse homotopies at a stalk spread after shrinking a lifted map.
Source: Stacks Project, Tag 09RE, affine proof's equality in the homotopy category;
Tag 0BC7 (2), finite-component homotopy calculation, and Tag 00CR.
(blueprint: lem-sc-perfect-open-stalk-inverse-homotopies-spread).

Proof: Work on V. Restriction preserves the finite-free retractions
and the support bounds. For each of the two stalk homotopies only finitely many
reverse-degree components can be nonzero. Sandwich each component between the
restricted finite-free retractions, represent its finitely many matrix entries
by sections on principal opens containing x inside V, and intersect these opens.
Sandwich the resulting maps back to the complex terms. The two homotopy equations
in each of the finitely many relevant degrees hold at the stalk. Sandwich their
errors into the finite free terms and use the germ equality criterion to shrink
once more until every error entry vanishes. Outside the support intervals the
terms are zero and the equations hold uniquely. The reverse-degree support gives
Homotopy.zero. Restrict g to W and identify iterated restriction with restriction
from U to W through the canonical slice-site comparison; its naturality identifies
both composites with the stated maps. The same construction handles zero terms,
disjoint support intervals and arbitrary non-Noetherian rings. No quasi-isomorphism
hypothesis is used; the two specified homotopies are the input. Affineness of U and V is
not needed. -/
theorem exists_affine_perfect_open_stalk_inverse_homotopies_spread
    (X : Scheme.{u}) (U : X.Opens) (x : X)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (f : P ⟶ Q) (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U)
    (g : ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).obj P)
    (hfg : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        ((((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f) ≫ g)) (𝟙 _)))
    (hgf : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (g ≫ (((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)).map f))) (𝟙 _))) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      ∃ (gW : R.obj Q ⟶ R.obj P),
        Nonempty (Homotopy (R.map f ≫ gW) (𝟙 _)) ∧
        Nonempty (Homotopy (gW ≫ R.map f) (𝟙 _)) := by
  let R₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)
  let R := R₀.mapHomologicalComplex (.up ℤ)
  have hfg' : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (R.map f ≫ g))
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (𝟙 (R.obj P)))) := by
    rw [CategoryTheory.Functor.map_id]
    exact hfg
  have hgf' : Nonempty (Homotopy
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (g ≫ R.map f))
      (((openModuleStalkFunctor X V ⟨x, hxV⟩).mapHomologicalComplex (.up ℤ)).map
        (𝟙 (R.obj Q)))) := by
    rw [CategoryTheory.Functor.map_id]
    exact hgf
  obtain ⟨A, hAV, hxA, _, ⟨hA⟩⟩ := exists_affine_perfect_open_stalk_homotopy_spread
    X U P hP x V hxV hVU (R.map f ≫ g) (𝟙 _) hfg' V le_rfl hxV
  obtain ⟨W, hWA, hxW, hW, ⟨hQW⟩⟩ := exists_affine_perfect_open_stalk_homotopy_spread
    X U Q hQ x V hxV hVU (g ≫ R.map f) (𝟙 _) hgf' A hAV hxA
  let B₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE (hWA.trans hAV))
  let B := B₀.mapHomologicalComplex (.up ℤ)
  let cA := Functor.mapHomologicalComplexCompIso
    (restriction_comp_iso X V A W hAV hWA) (.up ℤ)
  have hPW := (SheafOfModules.overMap (moduleRings X.toRingedSpace)
    (homOfLE hWA)).mapHomotopy hA
  have hPW' := homotopy_of_natIso cA.symm (R.map f ≫ g) (𝟙 _) hPW
  have hP' : Homotopy (B.map (R.map f) ≫ B.map g) (𝟙 _) := by
    rw [← B.map_comp, ← B.map_id (R.obj P)]
    exact hPW'
  have hQ' : Homotopy (B.map g ≫ B.map (R.map f)) (𝟙 _) := by
    rw [← B.map_comp, ← B.map_id (R.obj Q)]
    exact hQW
  let c := Functor.mapHomologicalComplexCompIso
    (restriction_comp_iso X U V W hVU (hWA.trans hAV)) (.up ℤ)
  obtain ⟨gW, hgW⟩ := inverse_homotopies_of_natIso c.symm f (B.map g) hP' hQ'
  exact ⟨W, hxW, hW, (hWA.trans hAV).trans hVU, gW, hgW⟩

end
end AlgebraicGeometry.Scheme
