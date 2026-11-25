/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude

/-!
# Morphisms to an injective object in the derived category

Let `C` be an abelian category and `I` an injective object of `C`, placed in degree `0`. This
file shows:

* `DerivedCategory.eq_zero_of_isGE_one_of_injective`: every morphism `X ⟶ I` from an object
  `X ∈ D^{≥ 1}` is zero;
* `DerivedCategory.bijective_comp_singleFunctor_of_injective`: if `u : E ⟶ P` is a morphism with
  `E` in the heart, `P ∈ D^{≥ 0}` and `H⁰(u)` an isomorphism, then precomposition with `u`,
  `Hom(P, I) ⟶ Hom(E, I)`, is bijective.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Every morphism from an object of `D^{≥ 1}` to an injective object `I` placed in degree `0`
is zero: `I` is a K-injective complex, and there are no nonzero morphisms of complexes from a
complex concentrated in degrees `≥ 1` to a complex concentrated in degree `0`. -/
lemma eq_zero_of_isGE_one_of_injective {X : DerivedCategory C} [X.IsGE 1] {I : C}
    [Injective I] (f : X ⟶ (singleFunctor C 0).obj I) : f = 0 := by
  obtain ⟨K, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE 1
  let L : CochainComplex C ℤ := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj I
  have hL (n : ℤ) : Injective (L.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n hn).injective
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L 0
  let e' : (singleFunctor C 0).obj I ≅
      Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :=
    (singleFunctorIsoCompQ C 0).app I ≪≫ (quotientCompQhIso C).symm.app L
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L).2
      ((quotientCompQhIso C).hom.app K ≫ e.inv ≫ f ≫ e'.hom)
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  have hg' : g' = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    by_cases hn : n = 0
    · subst hn
      exact (K.isZero_of_isStrictlyGE 1 0 (by omega)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n hn).eq_of_tgt _ _
  rw [hg', Functor.map_zero, Functor.map_zero] at hg
  rw [← cancel_epi e.inv, ← cancel_epi ((quotientCompQhIso C).hom.app K), ← cancel_mono e'.hom]
  simpa using hg.symm

/-- Let `E ⟶ P ⟶ Z ⟶ E[1]` be a distinguished triangle with `Z ∈ D^{≥ 1}`, and let `I` be an
injective object of `C`. Then precomposition with `E ⟶ P` is a bijection
`Hom(P, I) ≃ Hom(E, I)`: neither `Z` nor `Z[-1]` has nonzero morphisms to `I`
(`DerivedCategory.eq_zero_of_isGE_one_of_injective`). -/
lemma bijective_comp_singleFunctor_of_injective_of_isGE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) [T.obj₃.IsGE 1] (I : C) [Injective I] :
    Function.Bijective (fun h : T.obj₂ ⟶ (singleFunctor C 0).obj I ↦ T.mor₁ ≫ h) := by
  have : (T.obj₃⟦(-1 : ℤ)⟧).IsGE 2 := TStructure.t.isGE_shift T.obj₃ 1 (-1) 2 (by omega)
  have : (T.obj₃⟦(-1 : ℤ)⟧).IsGE 1 := TStructure.t.isGE_of_ge _ 1 2 (by omega)
  refine ⟨fun h₁ h₂ hh ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT (h₁ - h₂)
      (by simpa [Preadditive.comp_sub, sub_eq_zero] using hh)
    rw [hk, eq_zero_of_isGE_one_of_injective (X := T.obj₃) k, comp_zero]
  · obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) g
      (eq_zero_of_isGE_one_of_injective (X := T.obj₃⟦(-1 : ℤ)⟧) _)
    exact ⟨h, hh.symm⟩

/-- Let `u : E ⟶ P` be a morphism of `D(C)` with `E` in the heart, `P ∈ D^{≥ 0}` and `H⁰(u)` an
isomorphism, and let `I` be an injective object of `C`. Then precomposition with `u` is a
bijection `Hom(P, I) ≃ Hom(E, I)`: the cone of `u` lies in `D^{≥ 1}`
(`DerivedCategory.bijective_comp_singleFunctor_of_injective_of_isGE`). -/
lemma bijective_comp_singleFunctor_of_injective {E P : DerivedCategory C} [E.IsGE 0] [E.IsLE 0]
    [P.IsGE 0] (u : E ⟶ P) (hu : IsIso ((homologyFunctor C 0).map u)) (I : C) [Injective I] :
    Function.Bijective (fun h : P ⟶ (singleFunctor C 0).obj I ↦ u ≫ h) := by
  obtain ⟨Z, v, w, hT⟩ := distinguished_cocone_triangle u
  have hZ : Z.IsGE 1 := by
    rw [isGE_iff]
    intro i hi
    refine isZero_homology_obj₃_of_epi_of_mono _ hT i ?_ ?_
    · rcases (show i < 0 ∨ i = 0 by omega) with hi | rfl
      · exact epi_of_target_iso_zero _ (P.isZero_of_isGE 0 i hi).isoZero
      · exact inferInstanceAs (Epi ((homologyFunctor C 0).map u))
    · rcases lt_trichotomy (i + 1) 0 with hi' | hi' | hi'
      · exact mono_of_source_iso_zero _ (E.isZero_of_isGE 0 (i + 1) hi').isoZero
      · rw [hi']
        exact inferInstanceAs (Mono ((homologyFunctor C 0).map u))
      · exact mono_of_source_iso_zero _ (E.isZero_of_isLE 0 (i + 1) hi').isoZero
  have : (Triangle.mk u v w).obj₃.IsGE 1 := hZ
  exact bijective_comp_singleFunctor_of_injective_of_isGE _ hT I


end DerivedCategory
