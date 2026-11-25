/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation

/-! # A generically nonempty closed subset has nonempty nearby fibres

Source: Stacks Project, Tag 055G, intersection-image argument.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A single closed subset meeting the generic fibre meets every nearby fibre.

Source: Stacks Project, Tag 055G, argument for the nonempty intersections;
Tags 052A and 01UA.
Proof: the generic-point hypothesis makes T irreducible. Replace it by its reduction,
which is integral, and pull back P and C. Give C its reduced closed subscheme
structure. Its map to the reduced base is finite type since a closed immersion is
finite type. Its generic fibre is nonempty. Generic flatness, Tag 052A, gives a
nonempty affine open on which this map is flat and of finite presentation. Its
image is open by Tag 01UA and contains the generic point. This image is an open
neighbourhood on which every fibre meets C. Transfer it back to T along the
reduction homeomorphism. Fibres over corresponding points have the same underlying
sets, so the resulting open has the stated property. C cannot be empty by the
hypothesis; P need not be reduced or separated, and no assumption of noetherianity
on T is needed.

(blueprint: lem-sbc-generic-closed-subset-fibre-nonempty) -/
theorem exists_open_closed_subset_fibre_nonempty {P T : Scheme.{u}} (h : P ⟶ T)
    [LocallyOfFiniteType h] [QuasiCompact h] (η : T)
    (hη : IsGenericPoint η Set.univ) (C : Set P) (hC : IsClosed C)
    (hne : (C ∩ h ⁻¹' {η}).Nonempty) :
    ∃ V : Set T, IsOpen V ∧ η ∈ V ∧
      ∀ t ∈ V, (C ∩ h ⁻¹' {t}).Nonempty := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : TopologicalSpace.Closeds P)
  let f : I.subscheme ⟶ T := I.subschemeι ≫ h
  let j := T.nilradical.subschemeι
  have hj : Function.Surjective j := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.support_nilradical]
    rfl
  have hjhomeo : IsHomeomorph j :=
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
  let g : I.subscheme ⟶ T.nilradical.subscheme := f.liftNilradical
  have hgj : g ≫ j = f := f.liftNilradical_subschemeι
  have : LocallyOfFiniteType (g ≫ j) := by rw [hgj]; infer_instance
  have : QuasiCompact (g ≫ j) := by rw [hgj]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g j
  have : QuasiCompact g := QuasiCompact.of_comp g j
  obtain ⟨U, hU, hflat, hfp⟩ := exists_nonempty_open_flat_finitePresentation_restrict g
  have := hflat
  have := hfp
  have hηU : ηr ∈ U := (hηrg.mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηrange : ηr ∈ Set.range g := by
    obtain ⟨x, hxC, hxη⟩ := hne
    have hxI : x ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      simpa [I] using hxC
    obtain ⟨z, rfl⟩ := hxI
    refine ⟨z, j.isEmbedding.injective ?_⟩
    rw [hηr, ← Scheme.Hom.comp_apply, hgj]
    simpa [f, Scheme.Hom.comp_apply] using hxη
  have hηrestricted : (⟨ηr, hηU⟩ : U) ∈ Set.range (g ∣_ U) := by
    obtain ⟨z, hz⟩ := hηrange
    exact ⟨⟨z, show g z ∈ U by rw [hz]; exact hηU⟩, Subtype.ext (by simpa using hz)⟩
  let W : Set T.nilradical.subscheme := U.ι '' Set.range (g ∣_ U)
  have hW : IsOpen W := U.ι.isOpenEmbedding.isOpenMap _ (g ∣_ U).isOpenMap.isOpen_range
  refine ⟨j '' W, hjhomeo.isOpenMap _ hW, ⟨ηr, ⟨⟨ηr, hηU⟩, hηrestricted, rfl⟩, hηr⟩, ?_⟩
  rintro t ⟨s, ⟨v, ⟨z, rfl⟩, rfl⟩, rfl⟩
  refine ⟨I.subschemeι z.1, ?_, ?_⟩
  · have hz : I.subschemeι z.1 ∈ Set.range I.subschemeι := ⟨z.1, rfl⟩
    rw [I.range_subschemeι] at hz
    simpa [I] using hz
  · change h (I.subschemeι z.1) = j (U.ι ((g ∣_ U) z))
    simpa only [f, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply,
      morphismRestrict_base_coe] using (congrArg (fun k ↦ k z.1) hgj).symm

end AlgebraicGeometry
