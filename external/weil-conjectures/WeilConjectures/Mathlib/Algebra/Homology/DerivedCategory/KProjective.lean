/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Morphisms out of K-projective complexes in the derived category

A morphism `Q(K) ⟶ Q(L)` in the derived category out of a K-projective complex `K` is the
image of a morphism of complexes (`CochainComplex.IsKProjective.exists_Q_map_eq`).

A projective object placed in a single degree is K-projective
(`CochainComplex.isKProjective_singleFunctor_obj`). Hence, for a projective object `P` and `K`
in the derived category, there are no nonzero morphisms `P[0] ⟶ K[n]` if and only if there are
no nonzero morphisms `P ⟶ H^n(K)`
(`DerivedCategory.subsingleton_singleFunctor_hom_shift_iff_of_projective`). In particular, there
are no nonzero morphisms `P[0] ⟶ Q[n]` for objects `P`, `Q` with `P` projective and `n ≠ 0`
(`DerivedCategory.subsingleton_singleFunctor_hom_shift`).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A morphism `Q(K) ⟶ Q(L)` in the derived category out of a K-projective complex `K` is
the image of a morphism of complexes. -/
lemma IsKProjective.exists_Q_map_eq (K L : CochainComplex C ℤ) [K.IsKProjective]
    (g : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : K ⟶ L, DerivedCategory.Q.map φ = g := by
  obtain ⟨g', hg'⟩ := (IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).2
      ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ g ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality φ
  dsimp at h hg'
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K), ← h, hg']
  simp

omit [HasDerivedCategory.{w} C] in
/-- A projective object placed in a single degree is a K-projective complex. -/
instance isKProjective_singleFunctor_obj (P : C) [Projective P] (n : ℤ) :
    ((singleFunctor C n).obj P).IsKProjective := by
  have (m : ℤ) : Projective (((singleFunctor C n).obj P).X m) := by
    by_cases hm : m = n
    · subst hm
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) m P).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).projective
  exact isKProjective_of_projective _ n

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For a projective object `P` and `K` in the derived category, there are no nonzero
morphisms `P[0] ⟶ K[n]` if and only if there are no nonzero morphisms `P ⟶ H^n(K)`: the
single complex `P[0]` is K-projective, so the former are the cohomology classes of degree `n`
from `P[0]` to a representative of `K`. -/
lemma subsingleton_singleFunctor_hom_shift_iff_of_projective (P : C) [Projective P]
    (K : DerivedCategory C) (n : ℤ) :
    Subsingleton ((singleFunctor C 0).obj P ⟶ K⟦n⟧) ↔
      Subsingleton (P ⟶ (homologyFunctor C n).obj K) := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L : CochainComplex C ℤ, Nonempty (Q.obj L ≅ K) :=
    ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  let S := (CochainComplex.singleFunctor C 0).obj P
  let e₁ : ((singleFunctor C 0).obj P ⟶ K⟦n⟧) ≃
      ((HomotopyCategory.quotient C _).obj S ⟶ (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
    (Iso.homCongr ((singleFunctorIsoCompQ C 0).app P ≪≫ (quotientCompQhIso C).symm.app S)
      ((shiftFunctor _ n).mapIso e.symm ≪≫ (Q.commShiftIso n).symm.app L ≪≫
        (quotientCompQhIso C).symm.app _)).trans
      (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective S _)).symm
  rw [(e₁.trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := S) (L := L)
        (n := n)).toEquiv.symm).subsingleton_congr,
    (Iso.homCongr (Iso.refl P) ((homologyFunctor C n).mapIso e.symm ≪≫
      (homologyFunctorFactors C n).app L)).subsingleton_congr]
  exact (CochainComplex.subsingleton_cohomologyClass_singleFunctor_iff P L n).trans
    (L.subsingleton_hom_homology_iff_of_projective (i := n - 1) (j := n) (k := n + 1)
      (by simp) (by simp) P).symm

/-- There are no nonzero morphisms `P[0] ⟶ Q[b]` from a projective object `P` when `b ≠ 0`. -/
lemma subsingleton_singleFunctor_hom_shift (P : C) [Projective P] (Q : C) {b : ℤ} (hb : b ≠ 0) :
    Subsingleton ((singleFunctor C 0).obj P ⟶ ((singleFunctor C 0).obj Q)⟦b⟧) := by
  refine (subsingleton_singleFunctor_hom_shift_iff_of_projective P _ b).2 ⟨fun f g ↦ ?_⟩
  have : Limits.IsZero ((homologyFunctor C b).obj ((singleFunctor C 0).obj Q)) := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact isZero_of_isGE _ 0 b h
    · exact isZero_of_isLE _ 0 b h
  exact this.eq_of_tgt f g

end DerivedCategory
