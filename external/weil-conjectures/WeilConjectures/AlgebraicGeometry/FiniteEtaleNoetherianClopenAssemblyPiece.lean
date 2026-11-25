/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! The generic affine piece used in reduced Noetherian induction. -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Data for one generic affine piece and its strict closed complement
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-piece).

Proof data records the integral affine source, its generic open, the induced locally closed
image, and the strict closed-complement fields used by the induction theorem. -/
structure IntegralAffineGenericPiece (Y : Scheme.{u})
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (T : TopologicalSpace.Closeds Y) where
  B : Scheme.{u}
  isIntegral : IsIntegral B
  isNoetherian : IsNoetherian B
  isAffine : IsAffine B
  j : B ⟶ Y
  isImmersion : IsImmersion j
  W : B.Opens
  nonempty : Nonempty W
  property : P W.toScheme (W.ι ≫ j)
  range_subset : Set.range (W.ι ≫ j) ⊆ (T : Set Y)
  complement_closed : IsClosed ((T : Set Y) \ Set.range (W.ι ≫ j))
  strict_complement :
    (⟨(T : Set Y) \ Set.range (W.ι ≫ j), complement_closed⟩ :
      TopologicalSpace.Closeds Y) < T

/-- A nonempty closed induction piece contains an integral affine generic piece whose
complement is a strictly smaller closed subset. The proof is the irreducible-component
selection and affine-open avoidance argument from Tags 01OZ and 01J3
(blueprint: lem-a1-finite-etale-noetherian-clopen-assembly-piece).

Proof: choose an irreducible component meeting the closed subset, remove the other
components, choose an affine open in the remaining open, and apply the generic hypothesis.
The resulting open has a closed complement strictly below the induction subset. -/
theorem exists_integral_affine_generic_piece_avoiding_components
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y] [IsReduced Y]
    (P : (B : Scheme.{u}) → (B ⟶ Y) → Prop)
    (hgeneric : ∀ (B : Scheme.{u}) [IsIntegral B] [IsNoetherian B] [IsAffine B]
      (t : B ⟶ Y), IsImmersion t →
      ∃ U : B.Opens, Nonempty U ∧ P U.toScheme (U.ι ≫ t))
    (T : TopologicalSpace.Closeds Y) (hT : (T : Set Y) ≠ ∅) :
    Nonempty (IntegralAffineGenericPiece Y P T) := by
  classical
  letI : IsNoetherian Y := {}
  have hTne : (T : Set Y).Nonempty := Set.nonempty_iff_ne_empty.mpr hT
  obtain ⟨z, hz⟩ := hTne
  obtain ⟨C', hC', -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨z, hz⟩} : Set ((T : Set Y))) isIrreducible_singleton
  obtain ⟨o, ho, ⟨w, hwo⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      C' hC'
  obtain ⟨OX, hOX, hOXo⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp ho
  let C : Set Y := Subtype.val '' C'
  have hCcl : IsClosed C :=
    T.isClosed.isClosedMap_subtype_val _
      (isClosed_of_mem_irreducibleComponents C' hC')
  have hCirr : IsIrreducible C :=
    hC'.1.image _ continuous_subtype_val.continuousOn
  have hCT : C ⊆ (T : Set Y) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hTC : (T : Set Y) ∩ OX ⊆ C := by
    intro y hy
    change y ∈ (T : Set Y) ∧ y ∈ OX at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    have hyO : (⟨y, hy.1⟩ : (T : Set Y)) ∈ o := by
      rw [← hOXo]
      exact hy.2
    exact hoC hyO
  let I := IdealSheafData.vanishingIdeal ⟨C, hCcl⟩
  let ι := I.subschemeι
  have hrange : Set.range ι = C := by
    rw [IdealSheafData.range_subschemeι,
      IdealSheafData.coe_support_vanishingIdeal]
    rfl
  letI : IrreducibleSpace I.subscheme := by
    have h' : IrreducibleSpace (Set.range ι) := by
      rw [← isIrreducible_iff_irreducibleSpace, hrange]
      exact hCirr
    exact (Homeomorph.irreducibleSpace_iff ι.isEmbedding.toHomeomorph).mpr h'
  letI : IsReduced I.subscheme :=
    (IdealSheafData.reduced_induced_closed_subscheme Y ⟨C, hCcl⟩).2.2.2.1
  letI : IsIntegral I.subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  letI : IsNoetherian I.subscheme := isNoetherian_of_locallyOfFiniteType ι
  have hgen : IsGenericPoint (ι (genericPoint I.subscheme)) C := by
    have h := (genericPoint_spec I.subscheme).image ι.continuous
    rwa [Set.image_univ, hrange, hCcl.closure_eq] at h
  have hgen_mem_o : ι (genericPoint I.subscheme) ∈ OX := by
    apply (hgen.mem_open_set_iff hOX).mpr
    refine ⟨w, ?_, ?_⟩
    · exact ⟨w, hoC hwo, rfl⟩
    · rw [← hOXo] at hwo
      exact hwo
  let OI : I.subscheme.Opens := ι ⁻¹ᵁ ⟨OX, hOX⟩
  have hgen_mem_OI : genericPoint I.subscheme ∈ OI := by
    exact hgen_mem_o
  obtain ⟨R, f, hf, hxf, hfO⟩ :=
    exists_affine_mem_range_and_range_subset (X := I.subscheme)
      (x := genericPoint I.subscheme) hgen_mem_OI
  let B := Spec R
  let j : B ⟶ Y := f ≫ ι
  letI : Nonempty B := by
    obtain ⟨x, hx⟩ := hxf
    exact ⟨x⟩
  letI : IsIntegral B := isIntegral_of_isOpenImmersion f
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨W, hW, hP⟩ := hgeneric B (f ≫ ι) inferInstance
  obtain ⟨UI0, hUI0, hUI0W⟩ :=
    f.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let UI : Set I.subscheme := UI0 ∩ Set.range f
  have hUI : IsOpen UI := hUI0.inter (IsOpenImmersion.isOpen_range f)
  have hUIW : f ⁻¹' UI = (W : Set B) := by
    ext x
    change x ∈ f ⁻¹' UI0 ∧ x ∈ f ⁻¹' Set.range f ↔ x ∈ (W : Set B)
    rw [hUI0W]
    simp
  obtain ⟨UX0, hUX0, hUX0I⟩ :=
    ι.isEmbedding.isInducing.isOpen_iff.mp hUI
  let UX : Y.Opens := ⟨UX0 ∩ OX, hUX0.inter hOX⟩
  have hUX : IsOpen (UX : Set Y) := UX.2
  have hUXI : ι ⁻¹' (UX : Set Y) = UI ∩ OI := by
    ext x
    change x ∈ ι ⁻¹' UX0 ∧ x ∈ ι ⁻¹' OX ↔ x ∈ UI ∧ x ∈ OI
    rw [hUX0I]
    rfl
  have hrangeW : Set.range (W.ι ≫ j) = C ∩ (UX : Set Y) := by
    rw [show W.ι ≫ j = W.ι ≫ f ≫ ι by rfl]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    change (ι ∘ f) '' (W : Set B) = C ∩ (UX : Set Y)
    rw [← hUIW]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hfxUI : f x ∈ UI := hx
      have hfxOI : f x ∈ OI := hfO ⟨x, rfl⟩
      have hfxUX : ι (f x) ∈ (UX : Set Y) := by
        change f x ∈ ι ⁻¹' (UX : Set Y)
        rw [hUXI]
        exact ⟨hfxUI, hfxOI⟩
      exact ⟨hrange ▸ ⟨f x, rfl⟩, hfxUX⟩
    · rintro ⟨hyC, hyUX⟩
      rw [← hrange] at hyC
      obtain ⟨z, rfl⟩ := hyC
      have hzUI : ι ⁻¹' (UX : Set Y) ⊆ UI ∩ OI := by
        rw [hUXI]
      obtain ⟨hzUI, hzOI⟩ := hzUI hyUX
      obtain ⟨x, rfl⟩ := hzUI.2
      refine ⟨x, ⟨hzUI.1, ⟨x, rfl⟩⟩, rfl⟩
  have hsubW : Set.range (W.ι ≫ j) ⊆ (T : Set Y) := by
    rw [hrangeW]
    exact Set.inter_subset_left.trans hCT
  have hcomp_closed : IsClosed ((T : Set Y) \ Set.range (W.ι ≫ j)) := by
    rw [hrangeW]
    have hEq : (T : Set Y) \ (C ∩ UX) = (T : Set Y) ∩ (UX : Set Y)ᶜ := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · intro h
        exact ⟨h.1, by
          intro hy
          change y ∈ UX0 ∧ y ∈ OX at hy
          exact h.2 ⟨hTC ⟨h.1, hy.2⟩, hy⟩⟩
      · intro h
        exact ⟨h.1, fun hy => h.2 hy.2⟩
    rw [hEq]
    exact T.isClosed.inter hUX.isClosed_compl
  refine ⟨{
    B := B
    isIntegral := inferInstance
    isNoetherian := inferInstance
    isAffine := inferInstance
    j := j
    isImmersion := inferInstance
    W := W
    nonempty := hW
    property := hP
    range_subset := hsubW
    complement_closed := hcomp_closed
    strict_complement := ?_ }⟩
  apply lt_of_le_of_ne
  · intro y hy
    exact hy.1
  · intro heq
    obtain ⟨y, hy⟩ := hW
    let y' : W.toScheme := ⟨y, hy⟩
    have hy' : j (W.ι y') ∈ Set.range (W.ι ≫ j) := ⟨y', rfl⟩
    have hycomp : j (W.ι y') ∈
        (⟨(T : Set Y) \ Set.range (W.ι ≫ j), hcomp_closed⟩ :
          TopologicalSpace.Closeds Y) := by
      rw [heq]
      exact hsubW hy'
    exact hycomp.2 hy'

end AlgebraicGeometry.Scheme
