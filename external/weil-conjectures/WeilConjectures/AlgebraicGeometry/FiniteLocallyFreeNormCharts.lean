/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import Mathlib.RingTheory.Norm.Basic

/-!
# Local determinant charts for a finite locally free norm

Source: Stacks Project, Tag 03JE, final norm argument.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

open scoped TensorProduct in
/-- The determinant norm commutes with scalar extension. -/
private theorem norm_tmul_one
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.norm A (1 ⊗ₜ[R] a : A ⊗[R] S) = algebraMap R A (Algebra.norm R a) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange,
    Algebra.norm_apply]

open scoped TensorProduct in
/-- Affine restrictions give tensor-product section algebras, so norms restrict. -/
private theorem norm_restrict_affine
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsFinite s]
    {B C : X.Opens} (hB : IsAffineOpen B) (hC : IsAffineOpen C) (hCB : C ≤ B)
    (hfree : letI := (s.app B).hom.toAlgebra
      Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B))
    (a : Γ(Y, s ⁻¹ᵁ B)) :
    X.presheaf.map (homOfLE hCB).op
      (letI := (s.app B).hom.toAlgebra; Algebra.norm Γ(X, B) a) =
      (letI := (s.app C).hom.toAlgebra
       Algebra.norm Γ(X, C)
         (Y.presheaf.map (homOfLE (s.preimage_mono hCB)).op a)) := by
  have H : IsPullback (𝟙 Y) s s (𝟙 X) := IsPullback.of_id_fst
  have hpo := (isIso_pushoutSection_iff H (UY := s ⁻¹ᵁ C) (by simpa using hCB) le_rfl
    (by simp [inf_eq_right.mpr (s.preimage_mono hCB)])).mp
    (isIso_pushoutSection_of_isAffineOpen H (UY := s ⁻¹ᵁ C) (by simpa using hCB) le_rfl
      (by simp [inf_eq_right.mpr (s.preimage_mono hCB)]) hB hC (hB.preimage s))
  have hpo' : IsPushout (s.app B) (X.presheaf.map (homOfLE hCB).op)
      (Y.presheaf.map (homOfLE (s.preimage_mono hCB)).op) (s.app C) := by
    rw [← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE] at hpo
    simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using hpo
  let : Algebra Γ(X, B) Γ(Y, s ⁻¹ᵁ B) := (s.app B).hom.toAlgebra
  let : Algebra Γ(X, B) Γ(X, C) := (X.presheaf.map (homOfLE hCB).op).hom.toAlgebra
  let : Algebra Γ(Y, s ⁻¹ᵁ B) Γ(Y, s ⁻¹ᵁ C) :=
    (Y.presheaf.map (homOfLE (s.preimage_mono hCB)).op).hom.toAlgebra
  let : Algebra Γ(X, C) Γ(Y, s ⁻¹ᵁ C) := (s.app C).hom.toAlgebra
  let : Algebra Γ(X, B) Γ(Y, s ⁻¹ᵁ C) :=
    (s.app B ≫ Y.presheaf.map (homOfLE (s.preimage_mono hCB)).op).hom.toAlgebra
  have : IsScalarTower Γ(X, B) Γ(Y, s ⁻¹ᵁ B) Γ(Y, s ⁻¹ᵁ C) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, B) Γ(X, C) Γ(Y, s ⁻¹ᵁ C) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (s.app B ≫ Y.presheaf.map _).hom = (X.presheaf.map _ ≫ s.app _).hom
      rw [s.naturality]
      rfl)
  have : Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B) := hfree
  have : Module.Finite Γ(X, B) Γ(Y, s ⁻¹ᵁ B) := s.finite_app B hB
  have : Algebra.IsPushout Γ(X, B) Γ(Y, s ⁻¹ᵁ B) Γ(X, C) Γ(Y, s ⁻¹ᵁ C) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'
  have : Algebra.IsPushout Γ(X, B) Γ(X, C) Γ(Y, s ⁻¹ᵁ B) Γ(Y, s ⁻¹ᵁ C) :=
    Algebra.IsPushout.symm inferInstance
  let e := Algebra.IsPushout.equiv Γ(X, B) Γ(X, C) Γ(Y, s ⁻¹ᵁ B) Γ(Y, s ⁻¹ᵁ C)
  have he : e (1 ⊗ₜ a) = Y.presheaf.map (homOfLE (s.preimage_mono hCB)).op a := by
    simp only [e, Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  rw [← he, Algebra.norm_eq_of_algEquiv e, norm_tmul_one]
  rfl

/-- Restrict a norm of a section originally defined on a larger open. -/
private theorem norm_restrict_section
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsFinite s]
    {W B D : X.Opens} (hB : IsAffineOpen B) (hD : IsAffineOpen D)
    (hDB : D ≤ B) (hBW : B ≤ W)
    (hfree : letI := (s.app B).hom.toAlgebra
      Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B))
    (a : Γ(Y, s ⁻¹ᵁ W)) :
    X.presheaf.map (homOfLE hDB).op
      (letI := (s.app B).hom.toAlgebra
       Algebra.norm Γ(X, B) (Y.presheaf.map (homOfLE (s.preimage_mono hBW)).op a)) =
      (letI := (s.app D).hom.toAlgebra
       Algebra.norm Γ(X, D)
         (Y.presheaf.map (homOfLE (s.preimage_mono (hDB.trans hBW))).op a)) := by
  rw [norm_restrict_affine s hB hD hDB hfree]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp]
  rfl

/-- Check equality of chart norms on an affine cover of their possibly nonaffine overlap. -/
private theorem norm_charts_compatible
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsFinite s]
    {W B C : X.Opens} (hB : IsAffineOpen B) (hC : IsAffineOpen C)
    (hBW : B ≤ W) (hCW : C ≤ W)
    (hfreeB : letI := (s.app B).hom.toAlgebra
      Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B))
    (hfreeC : letI := (s.app C).hom.toAlgebra
      Module.Free Γ(X, C) Γ(Y, s ⁻¹ᵁ C))
    (a : Γ(Y, s ⁻¹ᵁ W)) :
    X.presheaf.map (homOfLE (inf_le_left : B ⊓ C ≤ B)).op
      (letI := (s.app B).hom.toAlgebra
       Algebra.norm Γ(X, B) (Y.presheaf.map (homOfLE (s.preimage_mono hBW)).op a)) =
    X.presheaf.map (homOfLE (inf_le_right : B ⊓ C ≤ C)).op
      (letI := (s.app C).hom.toAlgebra
       Algebra.norm Γ(X, C) (Y.presheaf.map (homOfLE (s.preimage_mono hCW)).op a)) := by
  classical
  have hlocal (z : ↥(B ⊓ C)) :
      ∃ D : X.Opens, z.1 ∈ D ∧ IsAffineOpen D ∧ D ≤ B ⊓ C := by
    obtain ⟨_, ⟨D, hD, rfl⟩, hzD, hDle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open z.2 (B ⊓ C).isOpen
    exact ⟨D, hzD, hD, hDle⟩
  choose D hzD hD hDle using hlocal
  have hcover : B ⊓ C ≤ ⨆ z, D z := by
    intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hzD ⟨z, hz⟩⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf D (B ⊓ C)
    (fun z ↦ homOfLE (hDle z)) hcover
  intro z
  change X.presheaf.map (homOfLE (hDle z)).op
      (X.presheaf.map (homOfLE (inf_le_left : B ⊓ C ≤ B)).op _) =
    X.presheaf.map (homOfLE (hDle z)).op
      (X.presheaf.map (homOfLE (inf_le_right : B ⊓ C ≤ C)).op _)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← X.presheaf.map_comp, ← X.presheaf.map_comp]
  exact (norm_restrict_section s hB (hD z) ((hDle z).trans inf_le_left) hBW hfreeB a).trans
    (norm_restrict_section s hC (hD z) ((hDle z).trans inf_le_right) hCW hfreeC a).symm

/-- Trivialize the finite locally free pushforward and refine inside the requested open. -/
private theorem exists_free_affine_chart
    {X Y : Scheme.{u}} (s : Y ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ (B : X.Opens), B ≤ W ∧ x ∈ B ∧ IsAffineOpen B ∧
      (letI := (s.app B).hom.toAlgebra
       Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B) ∧
       Module.Finite Γ(X, B) Γ(Y, s ⁻¹ᵁ B)) := by
  classical
  let M := (Scheme.Modules.pushforward s).obj (SheafOfModules.unit Y.ringCatSheaf)
  have : (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : M.IsFiniteLocallyFree := Scheme.Modules.isFiniteLocallyFree_pushforward s _
  obtain ⟨V, I, hI, hxV, ⟨e⟩⟩ := Scheme.Modules.exists_mem_over_iso_free M x
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hBVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ W from ⟨hxV, hx⟩)
      (V ⊓ W).isOpen
  refine ⟨B, le_trans hBVW inf_le_right, hxB, hB, ?_⟩
  let := (s.app B).hom.toAlgebra
  let e' := Scheme.Modules.sectionsLinearEquivOfOverIsoFree e (le_trans hBVW inf_le_left)
  have : Module.Free Γ(X, B) Γ(M, B) := Module.Free.of_equiv e'.symm
  exact ⟨inferInstanceAs (Module.Free Γ(X, B) Γ(M, B)), s.finite_app B hB⟩

/-- A section on the inverse image of an open has a norm, locally computed on finite
free affine charts.

Source: Stacks Project, Tag 03JE, final norm argument.

Proof: Restrict the finite flat locally finitely presented morphism to W. On an affine
neighbourhood of any point of W its source is affine, and its algebra is a finitely
presented flat module. Shrinking to affine principal neighbourhoods makes that module
finite free. On each such chart B take the determinant of multiplication by the
restriction of a. This is the finite free algebra norm Algebra.norm Γ(X, B). On overlaps these
sections agree: cover each overlap by affine principal neighbourhoods in both charts,
use compatibility of determinants with localization, and use invariance under change
of basis. The structure sheaf glues these sections to g on W. Its restriction to each
chart is the prescribed norm. The chart algebra is finite because s is finite.
There is no fixed rank assumption: the construction is local and determinants agree
on overlaps of every rank. If W is empty its section ring has a unique element and the
chart condition is vacuous. A chart with empty inverse image has the rank-zero algebra
and determinant 1, so it satisfies the same gluing condition.
(blueprint: lem-pd-finite-locally-free-norm-charts). -/
theorem exists_finiteLocallyFree_norm_charts
    {X Y : Scheme.{u}} (s : Y ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (W : X.Opens) (a : Γ(Y, s ⁻¹ᵁ W)) :
    ∃ g : Γ(X, W), ∀ x : X, x ∈ W →
      ∃ (B : X.Opens) (hBW : B ≤ W), x ∈ B ∧ IsAffineOpen B ∧
        (letI := (s.app B).hom.toAlgebra
         Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B) ∧
         Module.Finite Γ(X, B) Γ(Y, s ⁻¹ᵁ B) ∧
         X.presheaf.map (homOfLE hBW).op g =
           Algebra.norm Γ(X, B)
             (Y.presheaf.map (homOfLE (s.preimage_mono hBW)).op a)) := by
  classical
  have hcharts (x : W) := exists_free_affine_chart s W x.1 x.2
  choose B hBW hxB hB hfree using hcharts
  let n (x : W) : Γ(X, B x) :=
    letI := (s.app (B x)).hom.toAlgebra
    Algebra.norm Γ(X, B x) (Y.presheaf.map (homOfLE (s.preimage_mono (hBW x))).op a)
  have hcover : W ≤ ⨆ x, B x := by
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf B n := by
    intro x y
    exact norm_charts_compatible s (hB x) (hB y) (hBW x) (hBW y)
      (hfree x).1 (hfree y).1 a
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf B W
    (fun x ↦ homOfLE (hBW x)) hcover n hcompat
  refine ⟨g, fun x hx ↦ ?_⟩
  exact ⟨B ⟨x, hx⟩, hBW ⟨x, hx⟩, hxB ⟨x, hx⟩, hB ⟨x, hx⟩,
    (hfree ⟨x, hx⟩).1, (hfree ⟨x, hx⟩).2, hg ⟨x, hx⟩⟩

end AlgebraicGeometry
