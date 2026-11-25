/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Embedding.Extend
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Totalization of a single row

Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2.
(blueprint: lem-sp-double-complex-single-row-total-iso).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable abbrev row (L : CochainComplex C ℕ) (q : ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ((HomologicalComplex.single C (ComplexShape.up ℕ) q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L

section

variable [∀ K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
  K.HasTotal (ComplexShape.up ℕ)]

private noncomputable def rowInclusion (L : CochainComplex C ℕ) (q i : ℕ) :
    L.X i ⟶ ((row L q).total (ComplexShape.up ℕ)).X (i + q) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) q (L.X i)).inv ≫
    (row L q).ιTotal (ComplexShape.up ℕ) i q (i + q) rfl

private theorem rowInclusion_isIso (L : CochainComplex C ℕ) (q i : ℕ) :
    IsIso (rowInclusion L q i) := by
  classical
  let g : ((row L q).total (ComplexShape.up ℕ)).X (i + q) ⟶ L.X i :=
    (row L q).totalDesc (c₁₂ := ComplexShape.up ℕ) (fun a b h ↦
    if hb : b = q then
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ) q (L.X a) b hb).hom ≫
        (L.XIsoOfEq (show a = i by change a + b = i + q at h; omega)).hom
    else 0)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · simp [rowInclusion, g, HomologicalComplex.singleObjXSelf]
  · apply HomologicalComplex₂.total.hom_ext
    intro a b h
    by_cases hb : b = q
    · subst b
      have ha : a = i := by change a + q = i + q at h; omega
      subst a
      simp [g, rowInclusion, row, HomologicalComplex.singleObjXSelf]
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℕ) q (L.X a) b hb).eq_of_src _ _

private theorem row_total_isZero (L : CochainComplex C ℕ) (q n : ℕ)
    (hn : ∀ i : ℕ, i + q ≠ n) :
    IsZero (((row L q).total (ComplexShape.up ℕ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  have hb : b ≠ q := by
    intro hb
    subst b
    exact hn a h
  exact (HomologicalComplex.isZero_single_obj_X
    (ComplexShape.up ℕ) q (L.X a) b hb).eq_of_src _ _

private noncomputable def rowXIso (L : CochainComplex C ℕ) (q n : ℕ) :
    (L.extend (ComplexShape.embeddingUp'Add (1 : ℕ) q)).X n ≅
      ((row L q).total (ComplexShape.up ℕ)).X n := by
  classical
  by_cases hn : ∃ i : ℕ, i + q = n
  · let i := n - q
    have hi : i + q = n := by obtain ⟨a, ha⟩ := hn; omega
    haveI := rowInclusion_isIso L q i
    exact L.extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) hi ≪≫
      asIso (rowInclusion L q i) ≪≫
        ((row L q).total (ComplexShape.up ℕ)).XIsoOfEq hi
  · exact IsZero.iso
      (L.isZero_extend_X (ComplexShape.embeddingUp'Add (1 : ℕ) q) n (by simpa using hn))
      (row_total_isZero L q n (by simpa using hn))

set_option backward.isDefEq.respectTransparency false in
private theorem rowXIso_hom (L : CochainComplex C ℕ) (q i : ℕ) :
    (rowXIso L q (i + q)).hom =
      (L.extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) rfl).hom ≫
        rowInclusion L q i := by
  classical
  dsimp [rowXIso]
  split_ifs with hn
  · have h : ∀ (a : ℕ) (ha : a = i) (han : a + q = i + q),
        (L.extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) han).hom ≫
          rowInclusion L q a ≫
            (((row L q).total (ComplexShape.up ℕ)).XIsoOfEq han).hom =
              (L.extendXIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) rfl).hom ≫
                rowInclusion L q i := by
      intro a ha han
      subst a
      simp [HomologicalComplex.XIsoOfEq]
    exact h _ (by omega) _
  · exact (hn ⟨i, rfl⟩).elim

set_option backward.isDefEq.respectTransparency false in
private theorem rowInclusion_comm (L : CochainComplex C ℕ) (q i j : ℕ)
    (hij : i + 1 = j) :
    rowInclusion L q i ≫ ((row L q).total (ComplexShape.up ℕ)).d (i + q) (j + q) =
      L.d i j ≫ rowInclusion L q j := by
  have hd : ((row L q).X i).d q (q + 1) = 0 := rfl
  dsimp [rowInclusion]
  rw [HomologicalComplex₂.total_d, CategoryTheory.Preadditive.comp_add,
    CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
    ι_D₁, ι_D₂, d₁_eq (row L q) (ComplexShape.up ℕ) hij q (j + q) rfl,
    d₂_eq' (row L q) (ComplexShape.up ℕ) i (show q + 1 = q + 1 from rfl)]
  rw [hd]
  simp [row, HomologicalComplex.single_map_f_self]


end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Totalization of a horizontal complex placed at vertical degree q is its
extension by zero along the degree translation p ↦ p+q.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2;
Stacks, Homology, lemma-ss-double-complex, item (5).
(blueprint: lem-sp-double-complex-single-row-total-iso).

Proof: in total degree n the summands are indexed by pairs (i,j) with i+j=n.
Every summand with j different from q is zero. If n is in the image of i ↦ i+q,
there is exactly one surviving summand, canonically L.X i; otherwise all summands
are zero. The coproduct universal property gives mutually inverse maps between
this diagonal and the degree-n term of the extension of L. The vertical
 differential vanishes since each column is a single-term complex. The horizontal
sign is +1, and its component on the surviving summand is L.d i (i+1).
Consequently these degreewise isomorphisms commute with the differentials and
assemble into an isomorphism of cochain complexes. This also covers q=0 and
n<q: translation is the identity for q=0, and both terms are zero for n<q. -/
theorem singleRow_total_iso
    [∀ K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      K.HasTotal (ComplexShape.up ℕ)]
    (L : CochainComplex C ℕ) (q : ℕ) :
    Nonempty (HomologicalComplex₂.total
      (((HomologicalComplex.single C (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L) (ComplexShape.up ℕ) ≅
        L.extend (ComplexShape.embeddingUp'Add (1 : ℕ) q)) := by
  classical
  refine ⟨(HomologicalComplex.Hom.isoOfComponents (rowXIso L q) ?_).symm⟩
  intro n m hnm
  by_cases hn : ∃ i : ℕ, i + q = n
  · obtain ⟨i, rfl⟩ := hn
    by_cases hm : ∃ j : ℕ, j + q = m
    · obtain ⟨j, rfl⟩ := hm
      have hij : i + 1 = j := by change i + q + 1 = j + q at hnm; omega
      rw [rowXIso_hom, rowXIso_hom, L.extend_d_eq (ComplexShape.embeddingUp'Add (1 : ℕ) q)
        (i := i) (j := j) (i' := i + q) (j' := j + q) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [rowInclusion_comm L q i j hij]
    · exact (row_total_isZero L q m (by simpa using hm)).eq_of_tgt _ _
  · exact (L.isZero_extend_X (ComplexShape.embeddingUp'Add (1 : ℕ) q) n
      (by simpa using hn)).eq_of_src _ _


end HomologicalComplex₂
