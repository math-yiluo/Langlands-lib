/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.LinearAlgebra.Span.Basic

/-! # The affine annihilation criterion
Source: Stacks Project, Tag 01PO, proof of clause (2).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

/-- On an affine open, global ideal annihilation implies local ideal annihilation.
Source: Stacks Project, Tag 01PO, proof of (2).
(blueprint: lem-weil-pbc-annihilator-affine-criterion).

Proof: for each smaller affine open W, quasi-coherent ideal data says J(W) is the
extension of J(U) along restriction. The ideal of scalars annihilating s restricted
to W contains the restrictions of J(U), hence contains J(W) by the map/comap
adjunction for ideals. For an arbitrary subopen V, cover V by all affine opens
contained in V. A section a of J on V restricts into J(W), by naturality of the
ideal inclusion and its sectionwise image formula. Thus the product of a with s
restricted to V vanishes on this affine cover. Separatedness of F makes it zero.
The reverse implication uses V = U. No finite-type or quasi-coherence hypothesis
on F is needed. Empty covers and the zero and unit ideals satisfy the same argument.
-/
theorem annihilator_affine_criterion (X : Scheme.{u}) (J : X.IdealSheafData)
    (F : X.Modules) (U : X.affineOpens) (s : Γ(F, U.1)) :
    (∀ (V : X.Opens) (h : V ≤ U.1), ∀ a ∈ J.idealOfOpens V,
      a • F.presheaf.map (homOfLE h).op s = 0) ↔ ∀ a ∈ J.ideal U, a • s = 0 := by
  constructor
  · intro hs a ha
    have h := hs U.1 le_rfl a (by simpa using ha)
    simpa using h
  · intro hs V hV a ha
    let A : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
    let I := {W : X.affineOpens // W.1 ≤ V}
    refine A.eq_of_locally_eq' (fun W : I ↦ W.val.val) V
      (fun W ↦ homOfLE W.property) ?_ _ 0 ?_
    · intro x hx
      obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWV⟩, hxW⟩
    · intro W
      rw [map_zero, F.map_smul]
      have haW : X.presheaf.map (homOfLE W.property).op a ∈ J.ideal W.val := by
        have ha' := ha
        change a ∈ (J.idealOfOpens V : Set Γ(X, V)) at ha'
        rw [← J.range_toModulesι_app_eq_idealOfOpens] at ha'
        obtain ⟨b, rfl⟩ := ha'
        rw [← J.idealOfOpens_eq_ideal]
        change _ ∈ (J.idealOfOpens W.val.val : Set Γ(X, W.val.val))
        rw [← J.range_toModulesι_app_eq_idealOfOpens]
        refine ⟨J.toModules.presheaf.map (homOfLE W.property).op b, ?_⟩
        exact ConcreteCategory.congr_hom
          (J.toModulesι.mapPresheaf.naturality (homOfLE W.property).op) b
      let t : Γ(F, W.val.val) := F.presheaf.map (homOfLE (W.property.trans hV)).op s
      let K : Ideal Γ(X, W.val.val) :=
        LinearMap.ker (LinearMap.toSpanSingleton Γ(X, W.val.val) Γ(F, W.val.val) t)
      have hle : J.ideal W.val ≤ K := by
        rw [← J.map_ideal (W.property.trans hV), Ideal.map_le_iff_le_comap]
        intro b hb
        change X.presheaf.map (homOfLE (W.property.trans hV)).op b • t = 0
        dsimp only [t]
        rw [← F.map_smul, hs b hb, map_zero]
      have hkill := hle haW
      change X.presheaf.map (homOfLE W.property).op a • t = 0 at hkill
      convert hkill using 1
      dsimp only [t]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl

end AlgebraicGeometry
