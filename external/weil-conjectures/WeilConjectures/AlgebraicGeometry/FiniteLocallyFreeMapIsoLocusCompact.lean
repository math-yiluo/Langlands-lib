/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen

/-! # Affine compactness of the isomorphism locus

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_affine_compact_isoLocus_neighbourhood {W : Scheme.{u}}
    (M N : W.Modules) [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    (V : W.Opens) (x : W) (hx : x ∈ V) :
    ∃ U : W.Opens, IsAffineOpen U ∧ U ≤ V ∧ x ∈ U ∧
      IsCompact ((U : Set W) ∩ (moduleMapIsoLocus φ : Set W)) := by
  obtain ⟨UM, I, hI, hxM, ⟨eM⟩⟩ := exists_mem_over_iso_free M x
  obtain ⟨UN, J, hJ, hxN, ⟨eN⟩⟩ := exists_mem_over_iso_free N x
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ V ⊓ UM ⊓ UN from ⟨⟨hx, hxM⟩, hxN⟩)
  have hUM : U ≤ UM := fun y hy ↦ (hUV hy).1.2
  have hUN : U ≤ UN := fun y hy ↦ (hUV hy).2
  let frameM : M.restrict U.ι ≅ SheafOfModules.free I :=
    restrictCompIso M UM.ι (W.homOfLE hUM) U.ι (W.homOfLE_ι hUM) ≪≫
      (restrictFunctor (W.homOfLE hUM)).mapIso (overIsoFreeEquiv M UM I eM) ≪≫
        restrictFreeIso (W.homOfLE hUM) I
  let frameN : N.restrict U.ι ≅ SheafOfModules.free J :=
    restrictCompIso N UN.ι (W.homOfLE hUN) U.ι (W.homOfLE_ι hUN) ≪≫
      (restrictFunctor (W.homOfLE hUN)).mapIso (overIsoFreeEquiv N UN J eN) ≪≫
        restrictFreeIso (W.homOfLE hUN) J
  obtain ⟨f, hf⟩ := moduleMapIsoLocus_inter_eq_basicOpen_of_free φ U frameM frameN
  refine ⟨U, hU, fun y hy ↦ (hUV hy).1.1, hxU, ?_⟩
  rw [hf]
  exact (hU.basicOpen f).isCompact

/-- On an affine open, the locally invertible locus of a vector bundle map is compact.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
(blueprint: lem-sc-finite-locally-free-map-iso-locus-compact)

Proof: Cover the affine open V by simultaneous finite free frames for M and N, refining
these frames to affine opens contained in V. Compactness of V gives a finite subcover.
On each frame with equal ranks, the locally invertible locus is the principal open of
its matrix determinant: the adjugate divided by the determinant is an inverse, and any
inverse forces the determinant to be a unit. On a frame with unequal ranks the locus
is empty, since an inverse at any point would give an isomorphism of residue vector
spaces of unequal dimensions. Thus the intersection with V is a finite union of
basic opens of these affine frames and is compact. The identification with moduleMapIsoLocus uses
its neighbourhood definition: every determinant open has an inverse; conversely,
invertibility on any neighbourhood implies invertibility on its stalks and hence the
same determinant condition. In rank zero the determinant is 1. Empty frames contribute
nothing, and no reducedness or global bound on the varying ranks is required. -/
theorem isCompact_moduleMapIsoLocus_inter {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    (V : W.Opens) (hV : IsAffineOpen V) :
    IsCompact ((V : Set W) ∩ (moduleMapIsoLocus φ : Set W)) := by
  classical
  choose U hU hUV hxU hcompact using
    fun x : V ↦ exists_affine_compact_isoLocus_neighbourhood M N φ V x x.2
  have hcover : (V : Set W) ⊆ ⋃ x : V, (U x : Set W) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hV.isCompact.elim_finite_subcover
    (fun x : V ↦ (U x : Set W)) (fun x ↦ (U x).isOpen) hcover
  have heq : (V : Set W) ∩ (moduleMapIsoLocus φ : Set W) =
      ⋃ x ∈ s, (U x : Set W) ∩ (moduleMapIsoLocus φ : Set W) := by
    ext x
    constructor
    · rintro ⟨hxV, hxφ⟩
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hxV)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi, hxφ⟩
    · intro hx
      obtain ⟨i, _, hxi, hxφ⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨hUV i hxi, hxφ⟩
  rw [heq]
  exact s.isCompact_biUnion fun x _ ↦ hcompact x

end AlgebraicGeometry.Scheme.Modules
