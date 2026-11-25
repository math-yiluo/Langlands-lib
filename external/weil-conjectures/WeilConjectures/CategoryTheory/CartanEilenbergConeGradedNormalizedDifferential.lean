/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedNormalizedIso
import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedAugmentationRepresentative
import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedResolutionRepresentative
/-! # Differential compatibility for the normalized column comparison

Source: Stacks Project, Homology, Tag 0133, canonical augmentation, and Tag 012X,
column filtration of a total complex. This is the augmented-cone refinement used
in the parent node's second proof step.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Normalized retained-column maps commute with one adjacent differential.
Source: Stacks Project, Tags 012X and 0133; parent comparison, step 3.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-normalized-differential).

Proof: precompose the asserted equality with the two inclusions of the column
cone. In negative resolution degrees both sources are zero, except for K in
cone degree -1. For an I term use the normalization lift in degree m. The
filtration arrow is monic and commutes with the cone differential, so its lift
has the same differential as its ambient diagonal inclusion. The horizontal
differential raises the complex index to p+1 and factors through step p+1;
its graded image is zero. The resolution differential preserves index p and
has coefficient one in the flipped total, and its lift in degree m+1 is the
one in the I normalization equation. On K in degree p-1, the -d_K term
raises index and vanishes in the quotient. The augmentation term is, by haug,
the resolution-zero column inclusion of (a.f p).f 0; normalization in degree p
identifies it with the off-diagonal column-cone differential. Extension by zero
kills all other components. Equality on the cone's jointly epic biproduct
inclusions proves the equality. This uses the specified lifts, never arbitrary
object isomorphisms. -/
theorem cartanEilenberg_cone_graded_normalized_differential
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
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m m' : ℤ) (hmm' : m + 1 = m')
    (e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p))
    (e' : (F.gradedPiece p).X m' ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m' - p))
    (he : CartanEilenbergConeGradedNormalized K I a aug F p m e)
    (he' : CartanEilenbergConeGradedNormalized K I a aug F p m' e') :
    e.inv ≫ (F.gradedPiece p).d m m' =
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).d
        (m - p) (m' - p) ≫ e'.inv := by
  let c : ((CochainComplex.single₀ A).obj (K.X p)).extend
      ComplexShape.embeddingUpNat ⟶ (I.X p).extend ComplexShape.embeddingUpNat :=
    HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat
  have hs : m - p + 1 = m' - p := by omega
  apply CochainComplex.mappingCone.ext_from c (m' - p) (m - p) hs
  · by_cases hm : m + 1 = p
    · obtain ⟨l, hl, hle⟩ := he.2 hm
      obtain ⟨l', hl', hle'⟩ := he'.1 0 (by omega)
      have hd := cartanEilenberg_cone_graded_augmentation_representative
        K I a b aug haug F hF p m m' hm hmm' l l' hl hl'
      let z := HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
        ComplexShape.embeddingUpNat (i := 0) (i' := m' - p)
        (by change (0 : ℤ) = m' - p; omega)
      apply (cancel_epi z.inv).1
      by_cases hb : p < b
      · exact (hKbelow p hb).eq_of_src _ _
      · rw [← Category.assoc, hle, Category.assoc, hle'] at hd
        simp only [Category.assoc] at hd
        rw [CochainComplex.mappingCone.inl_v_d_assoc c (m' - p) (m - p)
          (m' - p + 1) (by omega) (by omega)]
        change _ = z.inv ≫
          ((c.f (m' - p) ≫ (CochainComplex.mappingCone.inr c).f (m' - p) -
            (((CochainComplex.single₀ A).obj (K.X p)).extend
              ComplexShape.embeddingUpNat).d (m' - p) (m' - p + 1) ≫
            (CochainComplex.mappingCone.inl c).v (m' - p + 1) (m' - p) _) ≫ e'.inv)
        simp only [HomologicalComplex.extend_single_d, zero_comp, sub_zero]
        rw [HomologicalComplex.extendMap_f _ _ (i := 0)
          (by change (0 : ℤ) = m' - p; omega)]
        simp only [Category.assoc]
        change z.inv ≫ (CochainComplex.mappingCone.inl c).v (m' - p) (m - p) _ ≫
            e.inv ≫ (F.gradedPiece p).d m m' =
          z.inv ≫ z.hom ≫ (a.f p).f 0 ≫
            (HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
              (i := 0) (i' := m' - p) (by change (0 : ℤ) = m' - p; omega)).inv ≫
            (CochainComplex.mappingCone.inr c).f (m' - p) ≫ e'.inv
        rw [z.inv_hom_id_assoc]
        dsimp only [z, c]
        have htransport : ∀ (n n' : ℤ)
            (hn : ComplexShape.embeddingUpNat.f 0 = n)
            (hn' : ComplexShape.embeddingUpNat.f 0 = n')
            (hj : n + (-1) = m - p) (hj' : n' + (-1) = m - p),
            (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
              ComplexShape.embeddingUpNat hn).inv ≫
              (CochainComplex.mappingCone.inl c).v n (m - p) hj =
            (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
              ComplexShape.embeddingUpNat hn').inv ≫
              (CochainComplex.mappingCone.inl c).v n' (m - p) hj' := by
          intro n n' hn hn' hj hj'
          have h : n = n' := hn.symm.trans hn'
          cases h
          rfl
        rw [← Category.assoc, ← Category.assoc,
          htransport (m' - p) (m - p + 1) _ _ _ _, Category.assoc, Category.assoc]
        exact hd
    · have hz : IsZero (((CochainComplex.single₀ A).obj (K.X p)).extend
          ComplexShape.embeddingUpNat |>.X (m' - p)) := by
        exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (K.X p) (m' - p) (by omega)).of_iso
          ((HomologicalComplex.eval A (ComplexShape.up ℤ) (m' - p)).mapIso
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
              (K.X p) 0 0 rfl))
      exact hz.eq_of_src _ _
  · by_cases hm : 0 ≤ m - p
    · let r := (m - p).toNat
      have hr : (r : ℤ) + p = m := by dsimp [r]; rw [Int.toNat_of_nonneg hm]; omega
      obtain ⟨l, hl, hle⟩ := he.1 r hr
      obtain ⟨l', hl', hle'⟩ := he'.1 (r + 1) (by push_cast; omega)
      have hd := cartanEilenberg_cone_graded_resolution_representative
        K I b hIbelow aug F hF p m m' r hr hmm' l l' hl hl'
      let z := HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
        (i := r) (i' := m - p) (by change (r : ℤ) = m - p; omega)
      apply (cancel_epi z.inv).1
      rw [← Category.assoc, hle, Category.assoc, hle'] at hd
      simp only [Category.assoc] at hd
      rw [CochainComplex.mappingCone.inr_f_d_assoc]
      rw [HomologicalComplex.extend_d_eq _ _ (i := r) (j := r + 1)
        (by change (r : ℤ) = m - p; omega)
        (by change ((r + 1 : ℕ) : ℤ) = m' - p; push_cast; omega)]
      dsimp only [z, c]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using hd
    · have hz := HomologicalComplex.isZero_extend_X (I.X p)
        ComplexShape.embeddingUpNat (m - p) (by intro r; change (r : ℤ) ≠ m - p; omega)
      exact hz.eq_of_src _ _

end CategoryTheory.Functor
