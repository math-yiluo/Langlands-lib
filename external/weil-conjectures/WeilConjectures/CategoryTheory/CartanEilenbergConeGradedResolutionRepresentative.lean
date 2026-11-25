/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Differential of retained representatives in the cone filtration

Source: Stacks Project, Homology, Tags 012X and 0133, column filtration and
canonical augmentation; retained-summand calculation of the parent node.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The graded differential of a lifted resolution summand is its resolution differential.
Source: Stacks Project, Homology, Tag 012X (second filtration), with the cone
inclusion from Tag 0133; parent normalized-differential proof, I-term calculation.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-resolution-representative).

Proof: the quotient projection is a chain map. Cancel the monic inclusion of
step p to compute the differential of l in the ambient cone. The cone right
inclusion is a chain map. Expand the differential of the flipped total on its
(r,p) diagonal summand: it is the resolution differential, with coefficient one,
plus the signed complex-index differential to (r,p+1). By hl' the first term
is the inclusion of the resolution differential followed by l'. If p>=b,
the horizontal term factors through step p+1 by hF: its index p+1 belongs to
[max b (p+1),m']. The inclusions of successive steps commute with their ambient
inclusions, so monicity identifies the difference of the two lifts with this
factorization. The quotient kills it by the cokernel relation. If p<b the
source is zero by hIbelow, evaluated at r, and both sides are zero. The empty
interval case is thus covered as well. -/
theorem cartanEilenberg_cone_graded_resolution_representative
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m m' : ℤ) (r : ℕ) (hr : (r : ℤ) + p = m) (hmm' : m + 1 = m')
    (l : (I.X p).X r ⟶ (F.step p : CochainComplex A ℤ).X m)
    (l' : (I.X p).X (r + 1) ⟶ (F.step p : CochainComplex A ℤ).X m')
    (hl : l ≫ (F.step p).arrow.f m =
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
        ComplexShape.embeddingUpNat (i := r) (i' := m - p)
        (by change (r : ℤ) = m - p; omega)).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
      (CochainComplex.mappingCone.inr aug).f m)
    (hl' : l' ≫ (F.step p).arrow.f m' =
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
        ComplexShape.embeddingUpNat (i := r + 1) (i' := m' - p)
        (by change ((r + 1 : ℕ) : ℤ) = m' - p; push_cast; omega)).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) (m' - p) p m' (by change (m' - p) + p = m'; omega) ≫
      (CochainComplex.mappingCone.inr aug).f m') :
    l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫
        (F.gradedPiece p).d m m' =
      (I.X p).d r (r + 1) ≫ l' ≫
        (F.complexQuotientπ p (p + 1) (by omega)).f m' := by
  by_cases hb : b ≤ p
  · subst m'
    let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
    let q := F.complexQuotientπ p (p + 1) (by omega)
    let inc := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
    let u := J.ιTotal (ComplexShape.up ℤ) (m - p) (p + 1) (m + 1)
      (by change (m - p) + (p + 1) = m + 1; omega) ≫
      (CochainComplex.mappingCone.inr aug).f (m + 1)
    have hu : imageSubobject u ≤ F.complexStep (p + 1) (m + 1) := by
      rw [hF]
      apply le_trans _ le_sup_right
      have hmem : p + 1 ∈ Finset.Icc (max b (p + 1)) (m + 1) := by
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      have h := Finset.le_sup (f := fun s ↦ imageSubobject
        (J.ιTotalOrZero (ComplexShape.up ℤ) (m + 1 - s) s (m + 1) ≫
          (CochainComplex.mappingCone.inr aug).f (m + 1))) hmem
      rw [show m + 1 - (p + 1) = m - p by omega,
        J.ιTotalOrZero_eq _ _ _ _
          (by change (m - p) + (p + 1) = m + 1; omega)] at h
      exact h
    have hu' : imageSubobject u ≤ Subobject.mk ((F.step (p + 1)).arrow.f (m + 1)) := by
      simpa only [DecreasingFiltration.complexStep, imageSubobject_mono] using hu
    let t := factorThruImageSubobject u ≫
      Subobject.ofLEMk _ ((F.step (p + 1)).arrow.f (m + 1)) hu'
    have ht : t ≫ (F.step (p + 1)).arrow.f (m + 1) = u := by
      dsimp only [t]
      rw [Category.assoc, Subobject.ofLEMk_comp, imageSubobject_arrow_comp]
    have hi : inc.f (m + 1) ≫ (F.step p).arrow.f (m + 1) =
        (F.step (p + 1)).arrow.f (m + 1) :=
      congrArg (fun f ↦ f.f (m + 1))
        (Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)))
    have hiq : inc.f (m + 1) ≫ q.f (m + 1) = 0 :=
      congrArg (fun f ↦ f.f (m + 1)) (cokernel.condition inc)
    let z := HomologicalComplex.extendXIso
      (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
      ComplexShape.embeddingUpNat (i := r) (i' := m - p)
      (by change (r : ℤ) = m - p; omega)
    let w : (I.X p).X r ⟶ (J.X (m - p)).X (p + 1) := z.inv ≫ ((ComplexShape.up ℤ).ε (m - p) •
      (J.X (m - p)).d p (p + 1))
    have hd : l ≫ (F.step p : CochainComplex A ℤ).d m (m + 1) =
        (I.X p).d r (r + 1) ≫ l' + w ≫ t ≫ inc.f (m + 1) := by
      apply (cancel_mono ((F.step p).arrow.f (m + 1))).1
      rw [Preadditive.add_comp]
      simp only [Category.assoc, hi, ht]
      rw [← (F.step p).arrow.comm, ← Category.assoc, hl]
      dsimp only [w]
      simp only [Category.assoc]
      rw [CochainComplex.mappingCone.inr_f_d, HomologicalComplex₂.total_d,
        Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc,
        J.d₁_eq' _ (show (ComplexShape.up ℤ).Rel (m - p) (m - p + 1) by rfl),
        J.d₂_eq' _ (m - p) (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl)]
      have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (m - p, p) = 1 := rfl
      have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (m - p, p) = (ComplexShape.up ℤ).ε (m - p) := rfl
      rw [hε₁, hε₂, one_smul]
      congr 1
      · rw [hl']
        change z.inv ≫
            (((((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p)).extend
              ComplexShape.embeddingUpNat).d (m - p) (m - p + 1) ≫
              J.ιTotalOrZero (ComplexShape.up ℤ) (m - p + 1) p (m + 1)) ≫
              (CochainComplex.mappingCone.inr aug).f (m + 1) = _
        rw [HomologicalComplex.extend_d_eq _ _ (i := r) (j := r + 1)
          (by change (r : ℤ) = m - p; omega)
          (by change ((r + 1 : ℕ) : ℤ) = m - p + 1; push_cast; omega)]
        dsimp only [z]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [J.ιTotalOrZero_eq _ _ _ _
          (by change (m - p + 1) + p = m + 1; omega)]
        have htransport : ∀ (n n' : ℤ)
            (hn : ComplexShape.embeddingUpNat.f (r + 1) = n)
            (hn' : ComplexShape.embeddingUpNat.f (r + 1) = n')
            (hj : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) (n, p) = m + 1)
            (hj' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) (n', p) = m + 1),
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
              ComplexShape.embeddingUpNat hn).inv ≫
              J.ιTotal (ComplexShape.up ℤ) n p (m + 1) hj =
            (HomologicalComplex.extendXIso
              (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
              ComplexShape.embeddingUpNat hn').inv ≫
              J.ιTotal (ComplexShape.up ℤ) n' p (m + 1) hj' := by
          intro n n' hn hn' hj hj'
          have h : n = n' := hn.symm.trans hn'
          cases h
          rfl
        have ht' := htransport (m - p + 1) (m + 1 - p)
          (by change ((r + 1 : ℕ) : ℤ) = m - p + 1; push_cast; omega)
          (by change ((r + 1 : ℕ) : ℤ) = m + 1 - p; push_cast; omega)
          (by change (m - p + 1) + p = m + 1; omega)
          (by change (m + 1 - p) + p = m + 1; omega)
        rw [Functor.mapHomologicalComplex_obj_d, Functor.id_map]
        simpa only [Category.assoc] using congrArg
          (fun f ↦ (I.X p).d r (r + 1) ≫ f ≫
            (CochainComplex.mappingCone.inr aug).f (m + 1)) ht'
      · dsimp only [u, z]
        rw [J.ιTotalOrZero_eq _ _ _ _
          (by change (m - p) + (p + 1) = m + 1; omega)]
        simp only [Linear.units_smul_comp, Category.assoc]
    change l ≫ q.f m ≫ (F.complexQuotient p (p + 1) _).d m (m + 1) = _
    rw [q.comm, ← Category.assoc, hd, Preadditive.add_comp]
    simp only [Category.assoc, hiq, comp_zero, add_zero]
    rfl
  · have hz : IsZero ((I.X p).X r) :=
      (HomologicalComplex.eval A (ComplexShape.up ℕ) r).map_isZero
        (hIbelow p (by omega))
    exact hz.eq_of_src _ _

end CategoryTheory.Functor
