/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.FlatClosedFibreInterior

/-! # Spreading density of an open in ordinary fibres

Source: Stacks Project, Tag 054X, Lemma 37.24.3.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem dense_preimage_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (s : Set B) :
    Dense (e ⁻¹' s) ↔ Dense s := by
  constructor
  · intro h
    have h' := h.preimage e.symm.isOpenMap
    simpa only [Set.preimage_preimage, e.apply_symm_apply, Set.preimage_id'] using h'
  · exact fun h ↦ h.preimage e.isOpenMap

private theorem dense_fibre_homeomorph {X' X T' T : Scheme.{u}}
    (g : X' ⟶ T') (f : X ⟶ T) (i : X' ⟶ X) (j : T' ⟶ T)
    (hi : IsHomeomorph i) (hj : IsHomeomorph j) (h : g ≫ j = i ≫ f)
    (t : T') (W : X.Opens) :
    Dense ((g.fiberι t) ⁻¹' (i ⁻¹' (W : Set X))) ↔
      Dense ((f.fiberι (j t)) ⁻¹' (W : Set X)) := by
  let e : (g ⁻¹' {t}) ≃ₜ (f ⁻¹' {j t}) := hi.homeomorph.subtype (fun x ↦ by
    change g x = t ↔ f (i x) = j t
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact hj.injective.eq_iff.symm)
  let E := (g.fiberHomeo t).trans (e.trans (f.fiberHomeo (j t)).symm)
  have hE (x : g.fiber t) : f.fiberι (j t) (E x) = i (g.fiberι t x) := by
    simp [E, e]
  have heq : (g.fiberι t) ⁻¹' (i ⁻¹' (W : Set X)) =
      E ⁻¹' ((f.fiberι (j t)) ⁻¹' (W : Set X)) := by
    ext x
    simp only [Set.mem_preimage, hE]
  rw [heq]
  exact dense_preimage_homeomorph E _

private theorem flat_finitePresentation_restrict_le {X T : Scheme.{u}}
    (f : X ⟶ T) (U V : T.Opens) (hUV : U ≤ V)
    (hflat : Flat (f ∣_ V)) (hfp : LocallyOfFinitePresentation (f ∣_ V)) :
    Flat (f ∣_ U) ∧ LocallyOfFinitePresentation (f ∣_ U) := by
  have himage : V.ι ''ᵁ V.ι ⁻¹ᵁ U = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  constructor
  · have h : Flat ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hflat _
    have h' := (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp h
    rwa [himage] at h'
  · have h : LocallyOfFinitePresentation ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) :=
      IsZariskiLocalAtTarget.restrict hfp _
    have h' := (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp h
    rwa [himage] at h'

/-- An open subset dense in the generic fibre is dense in every ordinary fibre
on a neighbourhood of the generic point.

Source: Stacks Project, Tag 054X, Lemma 37.24.3.
Proof: give the closed complement Z of W its reduced induced scheme structure.
The assumption says that Z has nowhere dense generic fibre. Replace the base
by its reduction; the associated base changes are universal homeomorphisms,
so neither the assumption nor the conclusion changes. The reduced base is
integral because it has a generic point. Apply generic flatness and finite
presentation to X and Z, and intersect their generic neighbourhoods. Suppose
that Z_t has nonempty interior in X_t. Choose a generic point of a component
of X_t in that interior. Flatness of Z lifts it to a generalization in Z over
the generic point (Tag 03HV). Constancy of fibre dimension along this
specialization for flat locally finitely presented morphisms (Tag 054U,
Lemma 37.22.10) equates the dimensions of Z and X at the lifted point: at the
original point they agree because Z_t contains a neighbourhood. A component
of Z at the lifted point consequently has the dimension of a component of
X there, contradicting nowhere density in the generic fibre. Thus the
complement is nowhere dense in each fibre. Its open complement is dense.
The common nonempty base open contains the generic point; transport it back
through the reduction homeomorphism. Empty fibres satisfy density vacuously.

(blueprint: lem-sbc-generic-open-fibre-density) -/
theorem exists_open_fibre_dense_of_generic_dense {X T : Scheme.{u}}
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (W : X.Opens) (η : T) (hη : IsGenericPoint η Set.univ)
    (hdense : Dense ((f.fiberι η) ⁻¹' (W : Set X))) :
    ∃ U : T.Opens, η ∈ U ∧
      ∀ (t : T), t ∈ U → Dense ((f.fiberι t) ⁻¹' (W : Set X)) := by
  let i := X.nilradical.subschemeι
  let j := T.nilradical.subschemeι
  have hi : Function.Surjective i := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  have hj : Function.Surjective j := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  have hiHomeo : IsHomeomorph i :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isEmbedding, hi⟩
  have hjHomeo : IsHomeomorph j :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j.isEmbedding, hj⟩
  obtain ⟨ηr, hηr⟩ := hj η
  have hηrg : IsGenericPoint ηr (Set.univ : Set T.nilradical.subscheme) := by
    rw [isGenericPoint_iff_specializes]
    intro t
    simp only [Set.mem_univ, iff_true]
    apply j.isEmbedding.isInducing.specializes_iff.mp
    rw [hηr]
    exact hη.specializes (Set.mem_univ _)
  let : IrreducibleSpace T.nilradical.subscheme :=
    (irreducibleSpace_def _).mpr hηrg.isIrreducible
  let : IsIntegral T.nilradical.subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  let g := (i ≫ f).liftNilradical
  have hgj : g ≫ j = i ≫ f := (i ≫ f).liftNilradical_subschemeι
  have : LocallyOfFiniteType (g ≫ j) := by rw [hgj]; infer_instance
  have : QuasiCompact (g ≫ j) := by rw [hgj]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g j
  have : QuasiCompact g := QuasiCompact.of_comp g j
  let Wr : X.nilradical.subscheme.Opens := i ⁻¹ᵁ W
  let k := Wr.closedComplement
  obtain ⟨A, hA, hflatA, hfpA⟩ := exists_nonempty_open_flat_finitePresentation_restrict g
  obtain ⟨B, hB, hflatB, hfpB⟩ :=
    exists_nonempty_open_flat_finitePresentation_restrict (k ≫ g)
  have hηA : ηr ∈ A := (hηrg.mem_open_set_iff A.isOpen).mpr (by simpa using hA)
  have hηB : ηr ∈ B := (hηrg.mem_open_set_iff B.isOpen).mpr (by simpa using hB)
  let U : T.nilradical.subscheme.Opens := A ⊓ B
  have hηU : ηr ∈ U := ⟨hηA, hηB⟩
  obtain ⟨hflat, hfp⟩ :=
    flat_finitePresentation_restrict_le g U A inf_le_left hflatA hfpA
  obtain ⟨hflatZ, hfpZ⟩ :=
    flat_finitePresentation_restrict_le (k ≫ g) U B inf_le_right hflatB hfpB
  have hdenseR : Dense ((g.fiberι ηr) ⁻¹' (Wr : Set X.nilradical.subscheme)) := by
    apply (dense_fibre_homeomorph g f i j hiHomeo hjHomeo hgj ηr W).mpr
    rw [hηr]
    exact hdense
  have hrange : Set.range k = (Wr : Set X.nilradical.subscheme)ᶜ :=
    Wr.range_closedComplement
  have hgeneric : interior ((g.fiberι ηr) ⁻¹' Set.range k) = ∅ := by
    rw [interior_eq_empty_iff_dense_compl, hrange, Set.preimage_compl, compl_compl]
    exact hdenseR
  have hinterior :=
    interior_fibre_closed_eq_empty_of_flat_restrict g k ηr hηrg U hηU hgeneric
  let V : T.Opens := ⟨j '' (U : Set T.nilradical.subscheme),
    hjHomeo.isOpenMap _ U.isOpen⟩
  refine ⟨V, ⟨ηr, hηU, hηr⟩, ?_⟩
  rintro t ⟨s, hs, rfl⟩
  apply (dense_fibre_homeomorph g f i j hiHomeo hjHomeo hgj s W).mp
  have hclosed := hinterior s hs
  rw [interior_eq_empty_iff_dense_compl, hrange, Set.preimage_compl, compl_compl] at hclosed
  exact hclosed

end AlgebraicGeometry
