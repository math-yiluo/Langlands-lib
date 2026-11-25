/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import all WeilConjectures.CategoryTheory.FilteredQuotientPageMaps
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover

/-! # Descent between normalized quotient-page sequences

Source: Stacks Project, Homology, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-canonical-page-descent).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_homology_square
    {U V : WeilFilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential U.obj U.filtration r)
    (D' : FilteredComplexPageDifferential V.obj V.filtration r)
    (Dnext : FilteredComplexPageDifferential U.obj U.filtration (r + 1))
    (Dnext' : FilteredComplexPageDifferential V.obj V.filtration (r + 1))
    (pq : ℤ × ℤ)
    (e : D.page.homology pq ≅ filteredComplexPageObject U.obj U.filtration (r + 1) pq)
    (e' : D'.page.homology pq ≅ filteredComplexPageObject V.obj V.filtration (r + 1) pq)
    (he : FilteredComplexHomologyNormalized U.obj U.filtration r D pq e)
    (he' : FilteredComplexHomologyNormalized V.obj V.filtration r D' pq e') :
    HomologicalComplex.homologyMap (quotientPageMap t r D D') pq ≫ e'.hom =
      e.hom ≫ (quotientPageMap t (r + 1) Dnext Dnext').f pq := by
  let S := quotientPageSquares t r
  let T := quotientPageSquares t (r + 1)
  have hs (a : ℤ) : T.s a = S.s a :=
    (cancel_mono (V.filtration.step a).arrow).1 ((T.hs a).trans (S.hs a).symm)
  have hg : T.g pq.1 = S.g pq.1 := by
    have : Epi (U.filtration.complexQuotientπ pq.1 (pq.1 + 1) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    apply (cancel_epi (U.filtration.complexQuotientπ pq.1 (pq.1 + 1) (Int.le_add_one le_rfl))).1
    rw [T.hg, S.hg, hs]
  have hZU := filteredComplex_cycles_successor_le U.obj U.filtration r pq
  have hZV := filteredComplex_cycles_successor_le V.obj V.filtration r pq
  obtain ⟨f, hfepi, hf⟩ :=
    filteredComplex_successor_cycles_cover U.obj U.filtration r hr D pq hZU
  obtain ⟨f', _, hf'⟩ :=
    filteredComplex_successor_cycles_cover V.obj V.filtration r hr D' pq hZV
  have : Epi f := hfepi
  have hincl : T.kz pq ≫ Subobject.ofLE _ _ hZV =
      Subobject.ofLE _ _ hZU ≫ S.kz pq := by
    apply (cancel_mono (V.filtration.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, S.hkz]
    rw [← Category.assoc, Subobject.ofLE_arrow, T.hkz, hg]
  have hcycles : T.kz pq ≫ f' =
      f ≫ HomologicalComplex.cyclesMap (quotientPageMap t r D D') pq := by
    apply (cancel_mono (D'.page.iCycles pq)).1
    rw [Category.assoc, hf', Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc f, hf]
    change T.kz pq ≫ (Subobject.ofLE _ _ hZV ≫
        filteredComplexPageπ V.obj V.filtration r pq) =
      (Subobject.ofLE _ _ hZU ≫ filteredComplexPageπ U.obj U.filtration r pq) ≫ S.k pq
    rw [Category.assoc, S.hk, ← Category.assoc, ← Category.assoc, hincl]
  apply (cancel_epi (f ≫ D.page.homologyπ pq)).1
  calc
    _ = f ≫ HomologicalComplex.cyclesMap (quotientPageMap t r D D') pq ≫
        D'.page.homologyπ pq ≫ e'.hom := by
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    _ = T.kz pq ≫ filteredComplexPageπ V.obj V.filtration (r + 1) pq := by
      rw [← Category.assoc f, ← hcycles]
      simp only [Category.assoc, he' hZV f' hf']
    _ = filteredComplexPageπ U.obj U.filtration (r + 1) pq ≫
        (quotientPageMap t (r + 1) Dnext Dnext').f pq := (T.hk pq).symm
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun a ↦ a ≫ (quotientPageMap t (r + 1) Dnext Dnext').f pq)
          (he hZU f hf)).symm

set_option backward.isDefEq.respectTransparency false in
/-- A filtered map descends between spectral sequences whose page complexes and successor
comparisons are identified with the normalized concrete quotient construction.
No finiteness assumption on the filtration is made.
Source: Stacks Project, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-canonical-page-descent).

Proof. Restrict the map to each step, descend to graded pieces, restrict to graded
cycles, and descend modulo boundaries. The representative differential commutes with
these maps by the chain-map equation, checked on an epic representative cover.
The normalized successor comparison is natural: restrict the graded map also to
successor cycles, cancel the monic graded cycle inclusions, and then cancel the epic
successor-cycle cover followed by the homology projection. Conjugate these page maps
by the supplied complex isomorphisms. Naturality of homology and the normalization
square give the spectral-sequence compatibility. Finally cancel the target graded
cycle inclusion to compare any two representatives, and use the cokernel square.
All operations are finite limits and cokernels in a single degree. -/
theorem exists_filteredCanonical_page_descent
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K) (F' : DecreasingFiltration K')
    (E E' : CohomologicalSpectralSequence C 1)
    (D : ∀ (r : ℤ) (_hr : 1 ≤ r), FilteredComplexPageDifferential K F r)
    (D' : ∀ (r : ℤ) (_hr : 1 ≤ r), FilteredComplexPageDifferential K' F' r)
    (j : ∀ (r : ℤ) (hr : 1 ≤ r), E.page r hr ≅ (D r hr).page)
    (j' : ∀ (r : ℤ) (hr : 1 ≤ r), E'.page r hr ≅ (D' r hr).page)
    (hj : ∀ (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
      FilteredComplexHomologyNormalized K F r (D r hr) pq
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up' (r, 1 - r)) pq).mapIso
          (j r hr).symm ≪≫ E.iso r (r + 1) pq rfl hr ≪≫
          (HomologicalComplex.eval C (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
            (j (r + 1) (by omega))))
    (hj' : ∀ (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
      FilteredComplexHomologyNormalized K' F' r (D' r hr) pq
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up' (r, 1 - r)) pq).mapIso
          (j' r hr).symm ≪≫ E'.iso r (r + 1) pq rfl hr ≪≫
          (HomologicalComplex.eval C (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
            (j' (r + 1) (by omega))))
    (b : K ⟶ K')
    (hb : ∀ q : ℤ, ∃ s : (F.step q : CochainComplex C ℤ) ⟶
        (F'.step q : CochainComplex C ℤ), s ≫ (F'.step q).arrow = (F.step q).arrow ≫ b) :
    ∃ N : E ⟶ E',
      ∀ (A : C) (q p r : ℤ) (hr : 1 ≤ r)
        (x : A ⟶ (F.step q : CochainComplex C ℤ).X (q + p))
        (y : A ⟶ (F'.step q : CochainComplex C ℤ).X (q + p))
        (z : A ⟶ (F.complexCycles q (q + p) r : C))
        (z' : A ⟶ (F'.complexCycles q (q + p) r : C)),
        x ≫ (F.step q).arrow.f (q + p) ≫ b.f (q + p) =
          y ≫ (F'.step q).arrow.f (q + p) →
        z ≫ (F.complexCycles q (q + p) r).arrow =
          x ≫ (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
        z' ≫ (F'.complexCycles q (q + p) r).arrow =
          y ≫ (F'.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
        z ≫ filteredComplexPageπ K F r (q, p) ≫ (j r hr).inv.f (q, p) ≫
          (N.hom r hr).f (q, p) =
        z' ≫ filteredComplexPageπ K' F' r (q, p) ≫ (j' r hr).inv.f (q, p) := by
  classical
  let U : WeilFilteredObject (CochainComplex C ℤ) := ⟨K, F⟩
  let V : WeilFilteredObject (CochainComplex C ℤ) := ⟨K', F'⟩
  let t : U ⟶ V := ⟨b, hb⟩
  let m (r : ℤ) (hr : 1 ≤ r) := quotientPageMap t r (D r hr) (D' r hr)
  let N : E ⟶ E' :=
    { hom := fun r hr ↦ (j r hr).hom ≫ m r hr ≫ (j' r hr).inv
      comm := by
        intro r r' pq hrr' hr
        subst r'
        have h := quotient_homology_square t r hr (D r hr) (D' r hr)
          (D (r + 1) (by omega)) (D' (r + 1) (by omega)) pq _ _
          (hj r hr pq) (hj' r hr pq)
        change HomologicalComplex.homologyMap (m r hr) pq ≫
            (HomologicalComplex.homologyMap (j' r hr).inv pq ≫
              (E'.iso r (r + 1) pq rfl hr).hom ≫ (j' (r + 1) (by omega)).hom.f pq) =
          (HomologicalComplex.homologyMap (j r hr).inv pq ≫
            (E.iso r (r + 1) pq rfl hr).hom ≫ (j (r + 1) (by omega)).hom.f pq) ≫
              (m (r + 1) (by omega)).f pq at h
        have hh := congrArg (fun a ↦
          HomologicalComplex.homologyMap (j r hr).hom pq ≫ a ≫
            (j' (r + 1) (by omega)).inv.f pq) h
        simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp_assoc,
          Iso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp,
          ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
          Category.comp_id] at hh
        simpa only [HomologicalComplex.homologyMap_comp, HomologicalComplex.comp_f,
          Category.assoc, m] using hh }
  refine ⟨N, ?_⟩
  intro A q p r hr x y z z' hxy hz hz'
  let S := quotientPageSquares t r
  have hs := congrArg (fun f ↦ f.f (q + p)) (S.hs q)
  simp only [HomologicalComplex.comp_f] at hs
  have hys : x ≫ (S.s q).f (q + p) = y := by
    apply (cancel_mono ((F'.step q).arrow.f (q + p))).1
    rw [Category.assoc, hs]
    exact hxy
  have hg := congrArg (fun f ↦ f.f (q + p)) (S.hg q)
  simp only [HomologicalComplex.comp_f] at hg
  have hzmap : z ≫ S.kz (q, p) = z' := by
    apply (cancel_mono (F'.complexCycles q (q + p) r).arrow).1
    rw [Category.assoc, S.hkz, ← Category.assoc, hz, Category.assoc, hg]
    rw [← Category.assoc x, hys]
    exact hz'.symm
  change z ≫ filteredComplexPageπ K F r (q, p) ≫ (j r hr).inv.f (q, p) ≫
      ((j r hr).hom ≫ m r hr ≫ (j' r hr).inv).f (q, p) = _
  simp only [HomologicalComplex.comp_f]
  have hji := congrArg (fun a ↦ a.f (q, p)) (j r hr).inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hji
  rw [← Category.assoc ((j r hr).inv.f (q, p)), hji, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc]
  change ((z ≫ filteredComplexPageπ K F r (q, p)) ≫ S.k (q, p)) ≫ _ = _
  rw [Category.assoc z, S.hk, ← Category.assoc z, hzmap]
  exact Category.assoc _ _ _

end CategoryTheory
