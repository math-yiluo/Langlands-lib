/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Morphisms from a projective object placed in degree `0`

Let `P` be a projective object of an abelian category `C`. A morphism `P[0] ⟶ K` in the derived
category vanishes as soon as `H⁰(K) = 0`
(`DerivedCategory.eq_zero_of_isZero_homology_zero`): the single complex `P[0]` is K-projective,
so morphisms out of it are computed in the homotopy category, and a chain map `P[0] ⟶ K` lands in
the cycles `Z⁰(K)`, which are the image of `K⁻¹` when `H⁰(K) = 0`, so it lifts to a null-homotopy
by projectivity.
-/

@[expose] public section

open CategoryTheory Limits CochainComplex HomComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

instance (P : C) [Projective P] : ((CochainComplex.singleFunctor C 0).obj P).IsKProjective := by
  have (n : ℤ) : Projective (((CochainComplex.singleFunctor C 0).obj P).X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ 0 P n hn).projective
  exact isKProjective_of_projective _ 0

omit [HasDerivedCategory C] in
/-- Cohomology classes of degree `0` from a projective object placed in degree `0` to a complex
`K` with `H⁰(K) = 0` vanish. -/
lemma cohomologyClass_single_eq_zero (P : C) [Projective P] (K : CochainComplex C ℤ)
    (hK : K.ExactAt 0) (x : CohomologyClass ((CochainComplex.singleFunctor C 0).obj P) K 0) :
    x = 0 := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective c 0 (by simp) 1 (by simp)
  rw [CohomologyClass.mk_eq_zero_iff,
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by simp)]
  -- `f` lands in the cycles, which are the image of `K⁻¹` since `H⁰(K) = 0`
  have hK' := (K.exactAt_iff' (-1) 0 1 (by simp) (by simp)).1 hK
  exact ⟨hK'.liftFromProjective f hf, hK'.liftFromProjective_comp f hf⟩

/-- A morphism `P[0] ⟶ K` in the derived category from a projective object `P` placed in
degree `0` vanishes if `H⁰(K) = 0`. -/
lemma eq_zero_of_isZero_homology_zero (P : C) [Projective P] (K : DerivedCategory C)
    (hK : IsZero ((homologyFunctor C 0).obj K)) (φ : (singleFunctor C 0).obj P ⟶ K) : φ = 0 := by
  obtain ⟨K', ⟨e⟩⟩ : ∃ K', Nonempty (Q.obj K' ≅ K) := ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  have hK' : K'.ExactAt 0 := (K'.exactAt_iff_isZero_homology 0).2
    (hK.of_iso (((homologyFunctorFactors C 0).app K').symm ≪≫
      (homologyFunctor C 0).mapIso e))
  let S := (CochainComplex.singleFunctor C 0).obj P
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have h1 : Subsingleton (CohomologyClass S K' 0) :=
    ⟨fun x y ↦ by rw [cohomologyClass_single_eq_zero P K' hK' x,
      cohomologyClass_single_eq_zero P K' hK' y]⟩
  have h2 : Subsingleton (q.obj S ⟶ q.obj (K'⟦(0 : ℤ)⟧)) :=
    (CohomologyClass.toHom_bijective S K' 0).surjective.subsingleton
  have h3 : Subsingleton (q.obj S ⟶ q.obj K') :=
    (Iso.homCongr (Iso.refl _) (q.mapIso ((shiftFunctorZero _ ℤ).app K'))).symm.subsingleton
  have h4 : Subsingleton ((q ⋙ Qh).obj S ⟶ (q ⋙ Qh).obj K') :=
    (CochainComplex.IsKProjective.Qh_map_bijective S (q.obj K')).surjective.subsingleton
  have h5 : Subsingleton (Q.obj S ⟶ Q.obj K') :=
    (Iso.homCongr ((quotientCompQhIso C).app S) ((quotientCompQhIso C).app K')).symm.subsingleton
  have : φ ≫ e.inv = 0 := Subsingleton.elim (α := Q.obj S ⟶ Q.obj K') _ _
  simpa using this =≫ e.hom

end DerivedCategory
