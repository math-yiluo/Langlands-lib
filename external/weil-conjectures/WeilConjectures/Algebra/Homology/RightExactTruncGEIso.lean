/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Right exact functors commute with lower truncation

Source: Stacks Project, Tags 0118 and 0654, the explicit good truncation construction.
(blueprint: lem-pc-right-exact-truncge-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CochainComplex

private theorem projection_f_eq_opcycles
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    (K.πTruncGE n).f n = K.pOpcycles n ≫ (K.truncGEXIsoOpcycles n).inv := by
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ (i := 0) (by simp)]
  rw [HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    _ _ (i := 0) (i' := n) (by simp)
      (by simp [ComplexShape.boundaryGE_embeddingUpIntGE_iff])]
  simp [CochainComplex.truncGEXIsoOpcycles, HomologicalComplex.truncGEXIsoOpcycles]

private noncomputable def projectionIsCokernel
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ ((K.πTruncGE n).f n)
      (show K.d (n - 1) n ≫ (K.πTruncGE n).f n = 0 by
        rw [projection_f_eq_opcycles, ← Category.assoc, K.d_pOpcycles, zero_comp])) :=
  IsCokernel.cokernelIso _ _ (K.opcyclesIsCokernel (i := n - 1) (j := n) (by simp))
    (K.truncGEXIsoOpcycles n).symm (projection_f_eq_opcycles K n).symm

private theorem isIso_projection_f
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    (K : CochainComplex A ℤ) (n i : ℤ) (hi : n < i) :
    IsIso ((K.πTruncGE n).f i) := by
  have he : (ComplexShape.embeddingUpIntGE n).f (i - n).natAbs = i := by
    change n + ((i - n).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel]
  have hb : ¬ (ComplexShape.embeddingUpIntGE n).BoundaryGE (i - n).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ he]
  exact HomologicalComplex.isIso_restrictionToTruncGE' K _ _ hb

/-- An additive functor preserving finite colimits commutes with good lower truncation.
Source: Stacks Project, Tag 0118 (canonical truncation) and Tag 0654.
(blueprint: lem-pc-right-exact-truncge-iso).

Proof: In degrees below n both complexes are zero, since an additive functor
preserves zero objects. Above n both terms are F.obj (K.X i), with the same
mapped differentials. At n, the term on the left is F.obj (coker d^(n-1)), while
the term on the right is coker (F.map d^(n-1)). Preservation of cokernels gives
the term isomorphism. The differential leaving n is the unique map descending
from F.map d^n; the cokernel universal property proves compatibility with that
differential. All other differential squares are identities or zero squares.
These component isomorphisms assemble to an isomorphism of complexes. This
argument works for every integer n, arbitrary unbounded complexes, and zero
categories, with no exactness assumption on K and no preservation of kernels. -/
theorem nonempty_map_truncGE_iso
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (n : ℤ) :
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj (K.truncGE n) ≅
      CochainComplex.truncGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n) := by
  classical
  let L : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj K
  have term (i : ℤ) : ∃ e : F.obj ((K.truncGE n).X i) ≅ (L.truncGE n).X i,
      F.map ((K.πTruncGE n).f i) ≫ e.hom = (L.πTruncGE n).f i := by
    obtain hi | hi | hi := lt_trichotomy i n
    · have hz₁ := F.map_isZero ((K.truncGE n).isZero_of_isStrictlyGE n i hi)
      have hz₂ := (L.truncGE n).isZero_of_isStrictlyGE n i hi
      exact ⟨hz₁.iso hz₂, hz₂.eq_of_tgt _ _⟩
    · subst i
      let h₁ := (CokernelCofork.ofπ ((K.πTruncGE n).f n)
          (show K.d (n - 1) n ≫ (K.πTruncGE n).f n = 0 by
            rw [projection_f_eq_opcycles, ← Category.assoc, K.d_pOpcycles, zero_comp]))
      let hc₁ := h₁.mapIsColimit (projectionIsCokernel K n) F
      let hc₂ := projectionIsCokernel L n
      let e := hc₁.coconePointUniqueUpToIso hc₂
      exact ⟨e, hc₁.comp_coconePointUniqueUpToIso_hom hc₂ WalkingParallelPair.one⟩
    · have : IsIso ((K.πTruncGE n).f i) := isIso_projection_f K n i hi
      have : IsIso ((L.πTruncGE n).f i) := isIso_projection_f L n i hi
      refine ⟨(asIso (F.map ((K.πTruncGE n).f i))).symm ≪≫
        asIso ((L.πTruncGE n).f i), ?_⟩
      simp
  choose e he using term
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro i j hij
  have : Epi ((K.πTruncGE n).f i) := by
    dsimp only [CochainComplex.πTruncGE]
    infer_instance
  have : Epi (F.map ((K.πTruncGE n).f i)) := inferInstance
  apply (cancel_epi (F.map ((K.πTruncGE n).f i))).1
  rw [← Category.assoc, he i, (L.πTruncGE n).comm i j]
  change F.map (K.d i j) ≫ (L.πTruncGE n).f j =
    F.map ((K.πTruncGE n).f i) ≫ F.map ((K.truncGE n).d i j) ≫ (e j).hom
  rw [← Category.assoc, ← F.map_comp, (K.πTruncGE n).comm i j,
    F.map_comp, Category.assoc, he j]

end CochainComplex
