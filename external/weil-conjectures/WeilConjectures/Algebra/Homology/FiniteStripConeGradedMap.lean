/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

/-! # Explicit surviving diagonal map
Source: Stacks Project, Homology, Tag 0133; finite-strip cone refinement, step 3.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The surviving source inclusion, supported at `n = p - 1`. -/
noncomputable def finiteStripSourceInclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ)) (p n : ℤ) :
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p)).X
      (n - p + 1) ⟶ (CochainComplex.mappingCone b).X n :=
  if h : n + 1 = p then
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (A.X p)
      (n - p + 1) (by omega)).hom ≫
    (A.XIsoOfEq h.symm).hom ≫
    (CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)
  else 0

/-- The row cone's source and target inclusions into the ambient cone.
Source: Stacks, Tag 0133; finite-strip cone refinement, step 3.
(blueprint: def-sc-finite-strip-cone-graded-map) -/
noncomputable def finiteStripRowInclusion
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (A : CochainComplex C ℤ)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (p n : ℤ) :
    (CochainComplex.mappingCone (f p)).X (n - p) ⟶
      (CochainComplex.mappingCone b).X n :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod (f p) (n - p) (n - p + 1) rfl).hom ≫
    biprod.desc (finiteStripSourceInclusion K A b p n)
      (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
        (CochainComplex.mappingCone.inr b).f n)

/-- The explicit row inclusion lands in the filtration tail.
Source: Stacks, Tag 0133; finite-strip cone refinement, step 3.
(blueprint: def-sc-finite-strip-cone-graded-map)
Proof: the source generator belongs to the tail at `n+1=p`. The target generator
has vertical index `p` and belongs to the tail whenever its horizontal index is
in the strip. Outside the strip its source is zero. Add the two factorizations. -/
theorem finiteStripRowInclusion_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    (F.complexStep p n).Factors (finiteStripRowInclusion K A b f p n) := by
  have hsrc : (F.complexStep p n).Factors (finiteStripSourceInclusion K A b p n) := by
    unfold finiteStripSourceInclusion
    split_ifs with h
    · apply Subobject.factors_of_factors_right
      apply Subobject.factors_of_factors_right
      apply Subobject.factors_of_le _ (show imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) ≤
          F.complexStep p n by rw [hsteps, ite_eq_left (by omega)]; exact le_sup_left)
      simpa using imageSubobject_factors_comp_self
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) (𝟙 _)
    · exact Subobject.factors_zero
  have htgt : (F.complexStep p n).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
        (CochainComplex.mappingCone.inr b).f n) := by
    by_cases hi : n - p ∈ Finset.Ico (0 : ℤ) (r : ℤ)
    · apply Subobject.factors_of_le _ (show imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
          (CochainComplex.mappingCone.inr b).f n) ≤ F.complexStep p n by
        rw [hsteps]
        apply le_trans _ le_sup_right
        apply le_trans _ (Finset.le_sup (f := fun i ↦
          if p ≤ n - i then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
              (CochainComplex.mappingCone.inr b).f n) else ⊥) hi)
        have heq : n - (n - p) = p := by omega
        rw [heq]
        simp only [ite_eq_left le_rfl]
        exact le_rfl)
      simpa using imageSubobject_factors_comp_self
        (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ≫
          (CochainComplex.mappingCone.inr b).f n) (𝟙 _)
    · have hz := (HomologicalComplex.eval C (ComplexShape.up ℤ) p).map_isZero
        (hsupport (n - p) (by
          simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
          exact hi))
      rw [hz.eq_zero_of_src (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n)]
      simp only [zero_comp, Subobject.factors_zero]
  unfold finiteStripRowInclusion
  apply Subobject.factors_of_factors_right
  rw [biprod.desc_eq]
  apply Subobject.factors_add
  · exact Subobject.factors_of_factors_right _ hsrc
  · exact Subobject.factors_of_factors_right _ htgt

/-- The evaluated filtration inclusion has an invertible image factor. -/
theorem finiteStripStep_image_isIso
    (M : CochainComplex C ℤ) (F : DecreasingFiltration M) (p n : ℤ) :
    IsIso (factorThruImageSubobject ((F.step p).arrow.f n)) := by
  have : Mono ((F.step p).arrow.f n) := inferInstance
  have : Mono (factorThruImageSubobject ((F.step p).arrow.f n)) :=
    mono_of_mono_fac (imageSubobject_arrow_comp ((F.step p).arrow.f n))
  exact isIso_of_mono_of_epi _

/-- The canonical surviving diagonal map to the graded object, constructed by
factorization through the tail followed by its cokernel projection.
Source: Stacks, Tag 0133; finite-strip cone refinement, step 3.
(blueprint: def-sc-finite-strip-cone-graded-map) -/
noncomputable def finiteStripGradedMap
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ i : ℤ, i < 0 ∨ (r : ℤ) ≤ i → IsZero (K.X i))
    (A : CochainComplex C ℤ) (b : A ⟶ K.total (ComplexShape.up ℤ))
    (f : ∀ p : ℤ,
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X p) ⟶ K.flip.X p)
    (F : DecreasingFiltration (CochainComplex.mappingCone b))
    (hsteps : ∀ p n : ℤ, F.complexStep p n =
      (if p ≤ n + 1 then imageSubobject
        ((CochainComplex.mappingCone.inl b).v (n + 1) n (by omega)) else ⊥) ⊔
      (Finset.Ico (0 : ℤ) (r : ℤ)).sup (fun i ↦
        if p ≤ n - i then imageSubobject
          (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n ≫
            (CochainComplex.mappingCone.inr b).f n) else ⊥))
    (p n : ℤ) :
    (CochainComplex.mappingCone (f p)).X (n - p) ⟶ (F.gradedPiece p).X n :=
  letI := finiteStripStep_image_isIso (CochainComplex.mappingCone b) F p n
  (F.complexStep p n).factorThru (finiteStripRowInclusion K A b f p n)
    (finiteStripRowInclusion_factors K r hsupport A b f F hsteps p n) ≫
    inv (factorThruImageSubobject ((F.step p).arrow.f n)) ≫
    (F.complexQuotientπ p (p + 1) (by omega)).f n

end HomologicalComplex₂
