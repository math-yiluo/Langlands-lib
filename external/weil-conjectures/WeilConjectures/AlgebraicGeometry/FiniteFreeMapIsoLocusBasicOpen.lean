/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocusPullback
import WeilConjectures.AlgebraicGeometry.Modules.LocalInvertibleMinorBlockIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.ResidueField

/-! # The isomorphism locus in an affine finite free frame

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
(blueprint: lem-sc-finite-free-map-iso-locus-basic-open)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

-- Both pullback constructions are left adjoint to the same pushforward.
private theorem tensor_isIso_iff {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) :
    IsIso ((tensorPullback g).map φ) ↔ IsIso ((pullback g).map φ) := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  exact NatIso.isIso_map_iff (adj.leftAdjointUniq (pullbackPushforwardAdjunction g)) φ

-- An invertible pullback along an open immersion supplies its image neighbourhood.
private theorem mem_locus_of_isIso_open {X W : Scheme.{u}} (g : X ⟶ W)
    [IsOpenImmersion g] {M N : W.Modules} (φ : M ⟶ N)
    (hg : IsIso ((pullback g).map φ)) (x : X) : g x ∈ moduleMapIsoLocus φ := by
  have hi : IsIso ((pullback g.opensRange.ι).map φ) := by
    have e : pullback g.opensRange.ι ≅ pullback g ⋙ pullback g.isoOpensRange.inv :=
      pullbackCongr g.isoOpensRange_inv_comp.symm ≪≫
        (pullbackComp g.isoOpensRange.inv g).symm
    exact (NatIso.isIso_map_iff e φ).2 (by
      change IsIso ((pullback g.isoOpensRange.inv).map ((pullback g).map φ))
      infer_instance)
  exact (mem_moduleMapIsoLocus φ (g x)).2
    ⟨g.opensRange, (tensor_isIso_iff g.opensRange.ι φ).2 hi, ⟨x, rfl⟩⟩

-- Surjectivity on sections gives a unit square matrix over any section ring.
private theorem isIso_freeMatrix_det {X : Scheme.{u}} {I : Type u}
    [Fintype I] [DecidableEq I]
    (ψ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free I)
    [IsIso ψ] : IsUnit (freeMatrix ψ).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).1
  apply Matrix.mulVec_surjective_iff_isUnit.1
  intro c
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    (Hom.app ψ ⊤)).2 ((freeSectionsEquiv I).symm c)
  refine ⟨freeSectionsEquiv I b, ?_⟩
  rw [← freeSectionsEquiv_app, hb, LinearEquiv.apply_symm_apply]

-- Restriction and pullback have the same matrix in their canonical free frames.
private theorem freeMatrix_restrict {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] {I J : Type u} [DecidableEq J]
    (ψ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J) :
    freeMatrix ((restrictFreeIso g I).inv ≫ (restrictFunctor g).map ψ ≫
      (restrictFreeIso g J).hom) = (freeMatrix ψ).map g.appTop := by
  rw [restrictFreeIso, restrictFreeIso]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.app_inv, Iso.app_hom]
  rw [← (restrictFunctorIsoPullback g).inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  exact freeMatrix_pullback g ψ

-- The adjugate inverse exists over the determinant basic open.
private theorem basicOpen_det_subset_locus {W : Scheme.{u}} {M N : W.Modules}
    (φ : M ⟶ N) (U : W.Opens) {I : Type u} [Fintype I] [DecidableEq I]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free I) :
    (W.basicOpen (U.topIso.hom
      (freeMatrix (eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom)).det) : Set W) ⊆
        (moduleMapIsoLocus φ : Set W) := by
  let ψ := eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom
  let δ := (freeMatrix ψ).det
  let f := U.topIso.hom δ
  let V := U.toScheme.basicOpen δ
  intro x hx
  change x ∈ W.basicOpen f at hx
  have himage : U.ι ''ᵁ V = W.basicOpen f := by
    simpa only [f, V, ← CommRingCat.comp_apply, Iso.hom_inv_id,
      CommRingCat.id_apply] using U.ι_image_basicOpen_topIso_inv f
  rw [← himage] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hdet : IsUnit (freeMatrix ((restrictFreeIso V.ι I).inv ≫
      (restrictFunctor V.ι).map ψ ≫ (restrictFreeIso V.ι I).hom)).det := by
    rw [freeMatrix_restrict]
    change IsUnit ((V.ι.appTop.hom.mapMatrix (freeMatrix ψ)).det)
    rw [← V.ι.appTop.hom.map_det]
    exact U.toScheme.isUnit_ι_appTop_basicOpen δ
  have hi := local_invertible_minor_block_isIso _ hdet
  have hiψ : IsIso ((restrictFunctor V.ι).map ψ) := by
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi
  have hiφ : IsIso ((restrictFunctor V.ι).map ((restrictFunctor U.ι).map φ)) := by
      simpa only [ψ, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff] using hiψ
  have hip : IsIso ((pullback (V.ι ≫ U.ι)).map φ) := by
    have hrestrict : IsIso ((restrictFunctor (V.ι ≫ U.ι)).map φ) :=
      (NatIso.isIso_map_iff (restrictFunctorComp V.ι U.ι) φ).2 hiφ
    exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (V.ι ≫ U.ι)) φ).1 hrestrict
  exact mem_locus_of_isIso_open (V.ι ≫ U.ι) φ hip ⟨y, hy⟩

-- A residue-field point has singleton image in the invertibility locus.
private theorem isIso_free_fiber_at_locus {W : Scheme.{u}} {M N : W.Modules}
    (φ : M ⟶ N) (U : W.Opens) {I J : Type u}
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J)
    (y : U) (hy : (y : W) ∈ moduleMapIsoLocus φ) :
    IsIso ((pullback (U.toScheme.fromSpecResidueField y)).map
      (eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom)) := by
  let g := U.toScheme.fromSpecResidueField y
  have ht : IsIso ((tensorPullback (g ≫ U.ι)).map φ) := by
    apply isIso_tensorPullback_of_range_subset_moduleMapIsoLocus φ (g ≫ U.ι)
    rintro _ ⟨z, rfl⟩
    simpa [g, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hy
  have hp : IsIso ((pullback (g ≫ U.ι)).map φ) :=
    (tensor_isIso_iff (g ≫ U.ι) φ).1 ht
  have hc : IsIso ((pullback g).map ((pullback U.ι).map φ)) :=
    (NatIso.isIso_map_iff (pullbackComp g U.ι) φ).2 hp
  have hr : IsIso ((pullback g).map ((restrictFunctor U.ι).map φ)) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) (pullback g)) φ).2 hc
  simp only [Functor.map_comp]
  infer_instance

-- An invertible residue-field matrix has nonzero determinant.
private theorem locus_inter_subset_basicOpen_det {W : Scheme.{u}} {M N : W.Modules}
    (φ : M ⟶ N) (U : W.Opens) {I : Type u} [Fintype I] [DecidableEq I]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free I) :
    (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) ⊆
      (W.basicOpen (U.topIso.hom
        (freeMatrix (eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom)).det) : Set W) := by
  rintro x ⟨hxU, hxφ⟩
  let y : U := ⟨x, hxU⟩
  let g := U.toScheme.fromSpecResidueField y
  let ψ := eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom
  have hi : IsIso ((pullback g).map ψ) := isIso_free_fiber_at_locus φ U eM eN y hxφ
  let ψ' := (pullbackFreeIso g I).inv ≫ (pullback g).map ψ ≫ (pullbackFreeIso g I).hom
  have hd : IsUnit (freeMatrix ψ').det := isIso_freeMatrix_det ψ'
  have he : (freeMatrix ψ').det = g.appTop (freeMatrix ψ).det := by
    dsimp only [ψ']
    rw [freeMatrix_pullback]
    change (g.appTop.hom.mapMatrix (freeMatrix ψ)).det = _
    exact (g.appTop.hom.map_det _).symm
  rw [he] at hd
  have hfield := Scheme.isField_Γ_Spec (Field.toIsField (U.toScheme.residueField y))
  let := hfield.toField
  have hmem : y ∈ U.toScheme.basicOpen (freeMatrix ψ).det := by
    have hn := (g.appTop_ne_zero_iff_mem_basicOpen hfield
      (freeMatrix ψ).det default).1 hd.ne_zero
    simpa only [g, Scheme.fromSpecResidueField_apply] using hn
  have himage := U.ι_image_basicOpen_topIso_inv (U.topIso.hom (freeMatrix ψ).det)
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at himage
  rw [← himage]
  exact ⟨y, hmem, rfl⟩

-- The same residue-field pullback also rules out unequal frame ranks.
private theorem card_eq_of_mem_locus {W : Scheme.{u}} {M N : W.Modules}
    (φ : M ⟶ N) (U : W.Opens) {I J : Type u} [Fintype I] [Fintype J]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J)
    (y : U) (hy : (y : W) ∈ moduleMapIsoLocus φ) : Fintype.card I = Fintype.card J := by
  classical
  let g := U.toScheme.fromSpecResidueField y
  let ψ := eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN.hom
  have hi : IsIso ((pullback g).map ψ) := isIso_free_fiber_at_locus φ U eM eN y hy
  let ψ' := (pullbackFreeIso g I).inv ≫ (pullback g).map ψ ≫ (pullbackFreeIso g J).hom
  have hfield := Scheme.isField_Γ_Spec (Field.toIsField (U.toScheme.residueField y))
  let := hfield.toField
  let E := (freeSectionsEquiv I).symm.trans
    ((appLinearEquivOfIso (asIso ψ') ⊤).trans (freeSectionsEquiv J))
  simpa using E.finrank_eq

/-- In simultaneous finite free frames on an open, the locally invertible locus
is a basic open.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), local matrix argument, and
Tag 0BDP, final determinant sentence.
(blueprint: lem-sc-finite-free-map-iso-locus-basic-open)

Proof: Give the finite index types Fintype structures. If their cardinalities agree,
reindex the target frame to the source index type and form the square matrix of the
restricted map. Transfer its determinant from the global sections of the open subscheme
to the sections of W on U using U.topIso. On its basic open, restriction makes the
determinant a unit. The proved local_invertible_minor_block_isIso constructs the inverse
free-sheaf map. Transport through the frames and restriction composition, then identify
tensor pullback with ordinary pullback by uniqueness of left adjoints to pushforward.
An open immersion is isomorphic to its image open, so every point of this basic open
belongs to moduleMapIsoLocus.

Conversely, pull the map back along the residue-field point of any point of U in the
locus. Its image is contained in the locus, so the proved pullback preservation theorem
makes this map invertible. Pullback composition and the free frames identify its matrix
with the original matrix under the map on global sections. An invertible square
free-sheaf map is surjective on global sections; in free coordinates this means its
matrix is surjective, hence its determinant is a unit. Global sections of the spectrum
of the residue field form a field. Thus the evaluated determinant is nonzero, which is
precisely membership in the original determinant basic open.

If the cardinalities differ, take f = 0. A point of U in the locus would again give an
invertible residue-field pullback. The global section coordinates of its two free
sheaves are finite vector spaces indexed by I and J. The induced linear equivalence
forces equal cardinalities, a contradiction. Thus both sides are empty. Empty U and
rank zero are included. The argument does not use affineness of U. -/
theorem moduleMapIsoLocus_inter_eq_basicOpen_of_free {W : Scheme.{u}}
    {M N : W.Modules} (φ : M ⟶ N) (U : W.Opens)
    {I J : Type u} [Finite I] [Finite J]
    (eM : M.restrict U.ι ≅ SheafOfModules.free I)
    (eN : N.restrict U.ι ≅ SheafOfModules.free J) :
    ∃ f : W.presheaf.obj (.op U),
      (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) = (W.basicOpen f : Set W) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  by_cases h : Fintype.card I = Fintype.card J
  · let e : J ≃ I := Fintype.equivOfCardEq h.symm
    let eN' := eN ≪≫ (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      e.toIso
    let f := U.topIso.hom
      (freeMatrix (eM.inv ≫ (restrictFunctor U.ι).map φ ≫ eN'.hom)).det
    refine ⟨f, Set.Subset.antisymm ?_ ?_⟩
    · exact locus_inter_subset_basicOpen_det φ U eM eN'
    · intro x hx
      exact ⟨W.basicOpen_le f hx, basicOpen_det_subset_locus φ U eM eN' hx⟩
  · refine ⟨0, ?_⟩
    rw [W.basicOpen_zero]
    change (U : Set W) ∩ (moduleMapIsoLocus φ : Set W) = ∅
    apply Set.eq_empty_iff_forall_notMem.2
    rintro x ⟨hxU, hxφ⟩
    exact h (card_eq_of_mem_locus φ U eM eN ⟨x, hxU⟩ hxφ)

end AlgebraicGeometry.Scheme.Modules
