/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedShortComplex

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
/-- A map annihilating a subobject annihilates any map whose image lies in it. -/
private theorem comp_zero_of_image_le
    {A : Type uA} [Category.{vA} A] [Abelian A] {X Y Z : A}
    (f : X ⟶ Y) (S : Subobject Y) (g : Y ⟶ Z)
    (hf : imageSubobject f ≤ S) (hg : S.arrow ≫ g = 0) : f ≫ g = 0 := by
  have he : (factorThruImageSubobject f ≫ Subobject.ofLE _ S hf) ≫ S.arrow = f := by
    simp
  rw [← he, Category.assoc, hg, comp_zero]

/-- Bounds and graded-piece calculation for the constructed filtration.
Source: Stacks Project, Homology, Tag 0133.  On a fixed diagonal `n`, every
nonzero bicomplex summand has complex index between `b` and `n`, while the
cone's `K` summand has index `n+1`; hence the displayed image-sum is the whole
cone at step `b` and is zero at step `n+2`, including empty intervals.  For
the quotient of consecutive steps, all summands except those of index `p`
vanish.  The surviving differential is the column differential, and the
off-diagonal map is identified with `a.f p` by `haug` and the extension
isomorphism.  Reindexing degree `n` to `n-p` therefore identifies the graded
complex with the mapping cone of `extendMap (a.f p)`; applying homology gives
the asserted isomorphism.  This argument uses only canonical projections and
inclusions, so it also covers zero columns and all integer indices.
Source: Stacks Project, Homology, Tag 0133.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-properties). -/
theorem cartanEilenberg_cone_filtration_properties
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n))) :
    (∀ n : ℤ, F.complexStep b n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      ∀ p n : ℤ, Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).homology
            (n - p)) := by
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  have hJzero (r s : ℤ) (hs : s < b ∨ r < 0) : IsZero ((J.X r).X s) := by
    change IsZero (((((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (I.X s)).extend ComplexShape.embeddingUpNat).X r)
    rcases hs with hs | hr
    · exact (HomologicalComplex.eval A (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor A).map_isZero
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero (hIbelow s hs)))
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (by intro i hi; change (i : ℤ) = r at hi; omega)
  constructor
  · intro n
    constructor
    · let S := F.complexStep b n
      have : Epi S.arrow := Preadditive.epi_of_cancel_zero S.arrow (by
        intro Y g hg
        apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
        · rw [comp_zero]
          by_cases hb : b ≤ n + 1
          · apply comp_zero_of_image_le _ S g ?_ hg
            dsimp only [S]
            rw [hF, ite_eq_left hb]
            exact le_sup_left
          · exact (hKbelow (n + 1) (by omega)).eq_zero_of_src _
        · rw [comp_zero]
          apply HomologicalComplex₂.total.hom_ext
          intro r s hrs
          change r + s = n at hrs
          rw [comp_zero]
          by_cases hs : b ≤ s ∧ s ≤ n
          · have hmem : s ∈ Finset.Icc (max b b) n := by
              simpa only [max_self, Finset.mem_Icc] using hs
            have him := Finset.le_sup
              (f := fun s ↦ imageSubobject (J.ιTotalOrZero (ComplexShape.up ℤ)
                (n - s) s n ≫ (CochainComplex.mappingCone.inr aug).f n)) hmem
            have he : n - s = r := by omega
            rw [he, J.ιTotalOrZero_eq _ _ _ _ hrs] at him
            have hle : imageSubobject (J.ιTotal (ComplexShape.up ℤ) r s n hrs ≫
                (CochainComplex.mappingCone.inr aug).f n) ≤ S := by
              dsimp only [S]
              rw [hF]
              exact him.trans le_sup_right
            simpa only [Category.assoc] using comp_zero_of_image_le _ S g hle hg
          · exact (hJzero r s (by omega)).eq_zero_of_src _)
      have : IsIso S.arrow := isIso_of_mono_of_epi S.arrow
      exact Subobject.eq_top_of_isIso_arrow S
    · rw [hF, ite_eq_right (by omega)]
      have he : Finset.Icc (max b (n + 2)) n = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        simp only [Finset.mem_Icc] at hs
        have := le_max_right b (n + 2)
        omega
      rw [he]
      simp
  · intro p n
    obtain ⟨e⟩ := cartanEilenberg_cone_graded_shortComplex_iso
      K I a b hIbelow hKbelow aug haug F hF p n
    exact ⟨ShortComplex.homologyMapIso e⟩


end CategoryTheory.Functor
