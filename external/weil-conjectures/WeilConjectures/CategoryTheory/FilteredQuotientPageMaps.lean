/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover

/-!
# Canonical maps between concrete quotient pages

Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The four representative squares specify a map on quotient pages.
Source: Stacks Project, Tag 012K, Lemma 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps). -/
def FilteredQuotientPageMapProperty
    (U V : ObjectProperty.FullSubcategory
      (fun W : WeilFilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (t : U ⟶ V) (r : ℤ)
    (DU : FilteredComplexPageDifferential U.obj.obj U.obj.filtration r)
    (DV : FilteredComplexPageDifferential V.obj.obj V.obj.filtration r)
    (m : DU.page ⟶ DV.page) : Prop :=
  ∀ (p q : ℤ)
    (s : ∀ a : ℤ, (U.obj.filtration.step a : CochainComplex C ℤ) ⟶
      (V.obj.filtration.step a : CochainComplex C ℤ))
    (g : U.obj.filtration.gradedPiece p ⟶ V.obj.filtration.gradedPiece p)
    (kz : (U.obj.filtration.complexCycles p (p + q) r : C) ⟶
      (V.obj.filtration.complexCycles p (p + q) r : C))
    (k : filteredComplexPageObject U.obj.obj U.obj.filtration r (p, q) ⟶
        filteredComplexPageObject V.obj.obj V.obj.filtration r (p, q))
    (hs : ∀ i : ℤ, s i ≫ (V.obj.filtration.step i).arrow =
      (U.obj.filtration.step i).arrow ≫ t.hom.hom)
    (hg : U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
        s p ≫ V.obj.filtration.complexQuotientπ p (p + 1) (by omega))
    (hkz : kz ≫ (V.obj.filtration.complexCycles p (p + q) r).arrow =
      (U.obj.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q))
    (hk : filteredComplexPageπ U.obj.obj U.obj.filtration r (p, q) ≫ k =
        kz ≫ filteredComplexPageπ V.obj.obj V.obj.filtration r (p, q)),
    m.f (p, q) = k

private theorem subobject_preserves_pullback
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (P : Subobject Y) (Q : Subobject Y')
    (hPQ : P ≤ (Subobject.pullback b).obj Q) :
    (Subobject.pullback f).obj P ≤
      (Subobject.pullback a).obj ((Subobject.pullback g).obj Q) := by
  rw [← Subobject.pullback_comp, ← h, Subobject.pullback_comp]
  exact leOfHom ((Subobject.pullback f).map (homOfLE hPQ))

private theorem subobject_preserves_image
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (P : Subobject X) (Q : Subobject X')
    (hPQ : P ≤ (Subobject.pullback a).obj Q) :
    (Subobject.«exists» f).obj P ≤
      (Subobject.pullback b).obj ((Subobject.«exists» g).obj Q) := by
  apply leOfHom
  refine ((Subobject.existsPullbackAdj f).homEquiv _ _).symm ?_
  apply homOfLE
  rw [← Subobject.pullback_comp, h, Subobject.pullback_comp]
  exact hPQ.trans (leOfHom ((Subobject.pullback a).map
    ((Subobject.existsPullbackAdj g).unit.app Q)))

private theorem subobject_preserves_inf
    {X Y : C} (f : X ⟶ Y) (P P' : Subobject X) (Q Q' : Subobject Y)
    (h : P ≤ (Subobject.pullback f).obj Q)
    (h' : P' ≤ (Subobject.pullback f).obj Q') :
    P ⊓ P' ≤ (Subobject.pullback f).obj (Q ⊓ Q') := by
  apply Subobject.le_of_factors
  apply (pullback_factors_iff _ _ _).mpr
  apply (Subobject.inf_factors _).mpr
  constructor
  · exact (pullback_factors_iff _ _ _).mp
      (Subobject.factors_of_le _ (inf_le_left.trans h) (P ⊓ P').factors_self)
  · exact (pullback_factors_iff _ _ _).mp
      (Subobject.factors_of_le _ (inf_le_right.trans h') (P ⊓ P').factors_self)

private theorem subobject_preserves_sup
    {X Y : C} (f : X ⟶ Y) (P P' : Subobject X) (Q Q' : Subobject Y)
    (h : P ≤ (Subobject.pullback f).obj Q)
    (h' : P' ≤ (Subobject.pullback f).obj Q') :
    P ⊔ P' ≤ (Subobject.pullback f).obj (Q ⊔ Q') := by
  apply sup_le
  · exact h.trans (leOfHom ((Subobject.pullback f).map (homOfLE le_sup_left)))
  · exact h'.trans (leOfHom ((Subobject.pullback f).map (homOfLE le_sup_right)))

private theorem filtered_step_preserved
    {U V : WeilFilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (p n : ℤ) :
    U.filtration.complexStep p n ≤
      (Subobject.pullback (t.hom.f n)).obj (V.filtration.complexStep p n) := by
  obtain ⟨s, hs⟩ := t.preserves p
  have hf : ((Subobject.pullback (t.hom.f n)).obj
      (V.filtration.complexStep p n)).Factors ((U.filtration.step p).arrow.f n) := by
    apply (pullback_factors_iff _ _ _).mpr
    have hs' := congrArg (fun f ↦ f.f n) hs
    simp only [HomologicalComplex.comp_f] at hs'
    rw [← hs']
    exact imageSubobject_factors_comp_self _ _
  exact imageSubobject_le _ (Subobject.factorThru _ _ hf) (by simp)

private theorem filtered_graded_subobjects_preserved
    {U V : WeilFilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
      (V.filtration.step a : CochainComplex C ℤ))
    (hs : ∀ a, s a ≫ (V.filtration.step a).arrow =
      (U.filtration.step a).arrow ≫ t.hom)
    (p : ℤ) (g : U.filtration.gradedPiece p ⟶ V.filtration.gradedPiece p)
    (hg : U.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
      s p ≫ V.filtration.complexQuotientπ p (p + 1) (by omega)) (n r : ℤ) :
    U.filtration.complexCycles p n r ≤
        (Subobject.pullback (g.f n)).obj (V.filtration.complexCycles p n r) ∧
    U.filtration.complexBoundaries p n r ≤
        (Subobject.pullback (g.f n)).obj (V.filtration.complexBoundaries p n r) := by
  have hstep := filtered_step_preserved t
  have hd (a b : ℤ) : U.obj.d a b ≫ t.hom.f b = t.hom.f a ≫ V.obj.d a b :=
    (t.hom.comm a b).symm
  have hs' := congrArg (fun f ↦ f.f n) (hs p)
  simp only [HomologicalComplex.comp_f] at hs'
  have hg' := congrArg (fun f ↦ f.f n) hg
  simp only [HomologicalComplex.comp_f] at hg'
  constructor
  · unfold DecreasingFiltration.complexCycles
    apply subobject_preserves_image _ _ _ _ hg'
    apply subobject_preserves_pullback _ _ _ _ hs'.symm
    apply subobject_preserves_sup
    · apply subobject_preserves_inf
      · exact hstep p n
      · exact subobject_preserves_pullback _ _ _ _ (hd n (n + 1)) _ _
          (hstep (p + r) (n + 1))
    · exact hstep (p + 1) n
  · unfold DecreasingFiltration.complexBoundaries
    apply subobject_preserves_image _ _ _ _ hg'
    apply subobject_preserves_pullback _ _ _ _ hs'.symm
    apply subobject_preserves_sup
    · apply subobject_preserves_inf
      · exact hstep p n
      · exact subobject_preserves_image _ _ _ _ (hd (n - 1) n) _ _
          (hstep (p - r + 1) (n - 1))
    · exact hstep (p + 1) n

private structure QuotientPageSquares
    (U V : WeilFilteredObject (CochainComplex C ℤ)) (t : U ⟶ V) (r : ℤ) where
  s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
    (V.filtration.step a : CochainComplex C ℤ)
  hs : ∀ a, s a ≫ (V.filtration.step a).arrow = (U.filtration.step a).arrow ≫ t.hom
  g : ∀ p : ℤ, U.filtration.gradedPiece p ⟶ V.filtration.gradedPiece p
  hg : ∀ p, U.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g p =
    s p ≫ V.filtration.complexQuotientπ p (p + 1) (by omega)
  kz : ∀ pq : ℤ × ℤ, (U.filtration.complexCycles pq.1 (pq.1 + pq.2) r : C) ⟶
    (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r : C)
  hkz : ∀ pq, kz pq ≫ (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
    (U.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫ (g pq.1).f (pq.1 + pq.2)
  k : ∀ pq : ℤ × ℤ, filteredComplexPageObject U.obj U.filtration r pq ⟶
    filteredComplexPageObject V.obj V.filtration r pq
  hk : ∀ pq, filteredComplexPageπ U.obj U.filtration r pq ≫ k pq =
    kz pq ≫ filteredComplexPageπ V.obj V.filtration r pq

private noncomputable def quotientPageSquares
    {U V : WeilFilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (r : ℤ) :
    QuotientPageSquares U V t r := by
  classical
  choose s hs using t.preserves
  have hc (p : ℤ) :
      Subobject.ofLE _ _ (U.filtration.antitone_step (show p ≤ p + 1 by omega)) ≫ s p =
      s (p + 1) ≫
        Subobject.ofLE _ _ (V.filtration.antitone_step (show p ≤ p + 1 by omega)) := by
    apply (cancel_mono (V.filtration.step p).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, hs]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  let g (p : ℤ) : U.filtration.gradedPiece p ⟶ V.filtration.gradedPiece p :=
    cokernel.map _ _ (s (p + 1)) (s p) (hc p)
  have hg (p : ℤ) : U.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g p =
      s p ≫ V.filtration.complexQuotientπ p (p + 1) (by omega) := by
    exact cokernel.π_desc _ _ _
  have hp (p n : ℤ) := filtered_graded_subobjects_preserved t s hs p (g p) (hg p) n r
  have hz (pq : ℤ × ℤ) :
      (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r).Factors
        ((U.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫
          (g pq.1).f (pq.1 + pq.2)) :=
    (pullback_factors_iff _ _ _).mp
      (Subobject.factors_of_le _ (hp pq.1 (pq.1 + pq.2)).1
        (U.filtration.complexCycles pq.1 (pq.1 + pq.2) r).factors_self)
  let kz (pq : ℤ × ℤ) := Subobject.factorThru _ _ (hz pq)
  have hkz (pq : ℤ × ℤ) :
      kz pq ≫ (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
      (U.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫
        (g pq.1).f (pq.1 + pq.2) := Subobject.factorThru_arrow _ _ _
  have hb (pq : ℤ × ℤ) :
      (V.filtration.complexBoundaries pq.1 (pq.1 + pq.2) r).Factors
        ((U.filtration.complexBoundaries pq.1 (pq.1 + pq.2) r).arrow ≫
          (g pq.1).f (pq.1 + pq.2)) :=
    (pullback_factors_iff _ _ _).mp
      (Subobject.factors_of_le _ (hp pq.1 (pq.1 + pq.2)).2
        (U.filtration.complexBoundaries pq.1 (pq.1 + pq.2) r).factors_self)
  let kb (pq : ℤ × ℤ) := Subobject.factorThru _ _ (hb pq)
  have hbk (pq : ℤ × ℤ) :
      Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles U.obj U.filtration pq.1 (pq.1 + pq.2) r) ≫
          kz pq = kb pq ≫ Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles V.obj V.filtration pq.1 (pq.1 + pq.2) r) := by
    apply (cancel_mono (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
    rw [Category.assoc, hkz, ← Category.assoc, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow]
    exact (Subobject.factorThru_arrow _ _ _).symm
  let k (pq : ℤ × ℤ) : filteredComplexPageObject U.obj U.filtration r pq ⟶
      filteredComplexPageObject V.obj V.filtration r pq :=
    cokernel.map _ _ (kb pq) (kz pq) (hbk pq)
  exact ⟨s, hs, g, hg, kz, hkz, k, fun _ ↦ cokernel.π_desc _ _ _⟩

private theorem quotientPageSquares_unique
    {U V : WeilFilteredObject (CochainComplex C ℤ)} {t : U ⟶ V} {r : ℤ}
    (S : QuotientPageSquares U V t r) (p q : ℤ)
    (s : ∀ a : ℤ, (U.filtration.step a : CochainComplex C ℤ) ⟶
      (V.filtration.step a : CochainComplex C ℤ))
    (g : U.filtration.gradedPiece p ⟶ V.filtration.gradedPiece p)
    (kz : (U.filtration.complexCycles p (p + q) r : C) ⟶
      (V.filtration.complexCycles p (p + q) r : C))
    (k : filteredComplexPageObject U.obj U.filtration r (p, q) ⟶
      filteredComplexPageObject V.obj V.filtration r (p, q))
    (hs : ∀ a, s a ≫ (V.filtration.step a).arrow =
      (U.filtration.step a).arrow ≫ t.hom)
    (hg : U.filtration.complexQuotientπ p (p + 1) (by omega) ≫ g =
      s p ≫ V.filtration.complexQuotientπ p (p + 1) (by omega))
    (hkz : kz ≫ (V.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.complexCycles p (p + q) r).arrow ≫ g.f (p + q))
    (hk : filteredComplexPageπ U.obj U.filtration r (p, q) ≫ k =
      kz ≫ filteredComplexPageπ V.obj V.filtration r (p, q)) : S.k (p, q) = k := by
  have hs_eq (a : ℤ) : S.s a = s a :=
    (cancel_mono (V.filtration.step a).arrow).1 ((S.hs a).trans (hs a).symm)
  have : Epi (U.filtration.complexQuotientπ p (p + 1) (by omega)) := by
    unfold DecreasingFiltration.complexQuotientπ
    infer_instance
  have hg_eq : S.g p = g := by
    apply (cancel_epi (U.filtration.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl))).1
    rw [S.hg, hg]
    rw [hs_eq]
  have hkz_eq : S.kz (p, q) = kz := by
    apply (cancel_mono (V.filtration.complexCycles p (p + q) r).arrow).1
    rw [S.hkz, hkz, hg_eq]
  have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  apply (cancel_epi (filteredComplexPageπ U.obj U.filtration r (p, q))).1
  rw [S.hk, hk, hkz_eq]


private theorem quotientPageSquares_comm
    {U V : WeilFilteredObject (CochainComplex C ℤ)} {t : U ⟶ V} {r : ℤ}
    (S : QuotientPageSquares U V t r)
    (DU : FilteredComplexPageDifferential U.obj U.filtration r)
    (DV : FilteredComplexPageDifferential V.obj V.filtration r) (i j : ℤ × ℤ) :
    S.k i ≫ DV.d i j = DU.d i j ≫ S.k j := by
  by_cases hij : (ComplexShape.up' (r, 1 - r)).Rel i j
  · obtain ⟨A, a, b, x, y, hepi, hd, hx, hy⟩ :=
      filteredComplex_differential_representatives_cover U.obj U.filtration r i j hij
    have : Epi (filteredComplexPageπ U.obj U.filtration r i) := by
      unfold filteredComplexPageπ
      infer_instance
    have hs (pq : ℤ × ℤ) := congrArg (fun f ↦ f.f (pq.1 + pq.2)) (S.hs pq.1)
    simp only [HomologicalComplex.comp_f] at hs
    have hg (pq : ℤ × ℤ) := congrArg (fun f ↦ f.f (pq.1 + pq.2)) (S.hg pq.1)
    simp only [HomologicalComplex.comp_f] at hg
    have hdV : (a ≫ (S.s i.1).f (i.1 + i.2)) ≫
        (V.filtration.step i.1).arrow.f (i.1 + i.2) ≫
          V.obj.d (i.1 + i.2) (j.1 + j.2) =
        (b ≫ (S.s j.1).f (j.1 + j.2)) ≫
          (V.filtration.step j.1).arrow.f (j.1 + j.2) := by
      calc
        _ = a ≫ (U.filtration.step i.1).arrow.f (i.1 + i.2) ≫
            t.hom.f (i.1 + i.2) ≫ V.obj.d (i.1 + i.2) (j.1 + j.2) := by
          simpa only [Category.assoc] using congrArg
            (fun f ↦ a ≫ f ≫ V.obj.d (i.1 + i.2) (j.1 + j.2)) (hs i)
        _ = a ≫ (U.filtration.step i.1).arrow.f (i.1 + i.2) ≫
            U.obj.d (i.1 + i.2) (j.1 + j.2) ≫ t.hom.f (j.1 + j.2) := by
          rw [t.hom.comm]
        _ = b ≫ (U.filtration.step j.1).arrow.f (j.1 + j.2) ≫
            t.hom.f (j.1 + j.2) := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ t.hom.f (j.1 + j.2)) hd
        _ = _ := by
          simpa only [Category.assoc] using congrArg (fun f ↦ b ≫ f) (hs j).symm
    have hxV : (x ≫ S.kz i) ≫
        (V.filtration.complexCycles i.1 (i.1 + i.2) r).arrow =
        (a ≫ (S.s i.1).f (i.1 + i.2)) ≫
          (V.filtration.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) := by
      rw [Category.assoc, S.hkz, ← Category.assoc, hx, Category.assoc, hg]
      simp only [Category.assoc]
    have hyV : (y ≫ S.kz j) ≫
        (V.filtration.complexCycles j.1 (j.1 + j.2) r).arrow =
        (b ≫ (S.s j.1).f (j.1 + j.2)) ≫
          (V.filtration.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) := by
      rw [Category.assoc, S.hkz, ← Category.assoc, hy, Category.assoc, hg]
      simp only [Category.assoc]
    have hDU := DU.on_representatives A i j hij a b x y hd hx hy
    have hDV := DV.on_representatives A i j hij
      (a ≫ (S.s i.1).f (i.1 + i.2)) (b ≫ (S.s j.1).f (j.1 + j.2))
      (x ≫ S.kz i) (y ≫ S.kz j) hdV hxV hyV
    apply (cancel_epi (x ≫ filteredComplexPageπ U.obj U.filtration r i)).1
    calc
      _ = (x ≫ S.kz i) ≫ filteredComplexPageπ V.obj V.filtration r i ≫ DV.d i j := by
        simpa only [Category.assoc] using
          congrArg (fun f ↦ x ≫ f ≫ DV.d i j) (S.hk i)
      _ = (y ≫ S.kz j) ≫ filteredComplexPageπ V.obj V.filtration r j := hDV
      _ = (y ≫ filteredComplexPageπ U.obj U.filtration r j) ≫ S.k j := by
        simp only [Category.assoc, S.hk]
      _ = _ := by rw [← hDU]; simp only [Category.assoc]
  · rw [DU.shape i j hij, DV.shape i j hij, comp_zero, zero_comp]

private noncomputable def quotientPageMap
    {U V : WeilFilteredObject (CochainComplex C ℤ)} (t : U ⟶ V) (r : ℤ)
    (DU : FilteredComplexPageDifferential U.obj U.filtration r)
    (DV : FilteredComplexPageDifferential V.obj V.filtration r) : DU.page ⟶ DV.page where
  f := (quotientPageSquares t r).k
  comm' i j _ := quotientPageSquares_comm (quotientPageSquares t r) DU DV i j

set_option linter.unusedVariables false in
/-- The quotient page maps exist, obey the category laws, and are determined uniquely.
This statement constructs no successor-page comparison.
Source: Stacks Project, Tag 012K, Lemmas 12.24.2 and 12.24.4.
(blueprint: lem-sp-filtered-quotient-page-maps).

Proof. Restrict a filtered map to every step by its preservation property; these
restrictions are unique after the monic step inclusions. Descend to each graded
piece by the cokernel universal property. Preservation of the pullback defining
cycle representatives induces a map on their graded images. Preservation of the
boundary images makes it descend to the quotient Z_r/B_r. On the epic cover by
cycle representatives, the chain map equation shows that this quotient map
commutes with the representative differentials, hence gives a page chain map.
Cancel the monic cycle inclusion and epic quotient projection to show that any
four squares specify this same map. The squares for identity maps use identity
restrictions; the squares for composites use composites of restrictions. The same
cancellation proves the identity and composition laws. Finally the canonical
restrictions and descents provide squares for each filtered map, so the universal
square property determines every component, and therefore the whole family. -/
theorem filteredQuotient_page_maps
    (D : ∀ (U : ObjectProperty.FullSubcategory
      (fun W : WeilFilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (r : ℤ)
      (hr : 1 ≤ r),
      FilteredComplexPageDifferential U.obj.obj U.obj.filtration r) :
    ∃! m : ∀ {U V : ObjectProperty.FullSubcategory
      (fun W : WeilFilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)} (t : U ⟶ V)
        (r : ℤ) (hr : 1 ≤ r), (D U r hr).page ⟶ (D V r hr).page,
      (∀ U r hr, m (𝟙 U) r hr = 𝟙 _) ∧
      (∀ U V W (t : U ⟶ V) (t' : V ⟶ W) r hr,
        m (t ≫ t') r hr = m t r hr ≫ m t' r hr) ∧
      (∀ U V (t : U ⟶ V) r hr,
        FilteredQuotientPageMapProperty (C := C) U V t r (D U r hr) (D V r hr) (m t r hr)) := by
  classical
  let m : ∀ {U V : ObjectProperty.FullSubcategory
      (fun W : WeilFilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)}
      (t : U ⟶ V) (r : ℤ) (hr : 1 ≤ r), (D U r hr).page ⟶ (D V r hr).page :=
    fun t r hr ↦ quotientPageMap t.hom r (D _ r hr) (D _ r hr)
  refine ⟨m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro U r hr
    apply HomologicalComplex.Hom.ext
    funext pq
    rcases pq with ⟨p, q⟩
    change (quotientPageSquares (𝟙 U : U ⟶ U).hom r).k (p, q) = 𝟙 _
    apply quotientPageSquares_unique (quotientPageSquares (𝟙 U : U ⟶ U).hom r) p q
      (fun _ ↦ 𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    · intro a
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      simp
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp
    · simp
  · intro U V W t t' r hr
    apply HomologicalComplex.Hom.ext
    funext pq
    rcases pq with ⟨p, q⟩
    let S := quotientPageSquares t.hom r
    let T := quotientPageSquares t'.hom r
    change (quotientPageSquares (t ≫ t').hom r).k (p, q) = S.k (p, q) ≫ T.k (p, q)
    apply quotientPageSquares_unique (quotientPageSquares (t ≫ t').hom r) p q
      (fun a ↦ S.s a ≫ T.s a) (S.g p ≫ T.g p) (S.kz (p, q) ≫ T.kz (p, q))
      (S.k (p, q) ≫ T.k (p, q))
    · intro a
      change (S.s a ≫ T.s a) ≫ _ = _ ≫ (t.hom.hom ≫ t'.hom.hom)
      rw [Category.assoc, T.hs, ← Category.assoc, S.hs, Category.assoc]
    · rw [← Category.assoc, S.hg, Category.assoc, T.hg, ← Category.assoc]
    · rw [Category.assoc, T.hkz, ← Category.assoc, S.hkz]
      simp only [HomologicalComplex.comp_f, Category.assoc]
    · rw [← Category.assoc, S.hk, Category.assoc, T.hk]
      simp only [Category.assoc]
  · intro U V t r hr p q s g kz k hs hg hkz hk
    exact quotientPageSquares_unique (quotientPageSquares t.hom r) p q
      s g kz k hs hg hkz hk
  · intro m' h'
    funext U V t r hr
    apply HomologicalComplex.Hom.ext
    funext pq
    rcases pq with ⟨p, q⟩
    let S := quotientPageSquares t.hom r
    exact h'.2.2 U V t r hr p q S.s (S.g p) (S.kz (p, q)) (S.k (p, q))
      S.hs (S.hg p) (S.hkz (p, q)) (S.hk (p, q))


end CategoryTheory
