/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryPageNaturality
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison

/-! # Stationary CE comparisons at outer filtration bounds

Source: Stacks Project, Tag 012K, cycle and boundary formulas and graded cohomology.
(blueprint: lem-weil-pbc-ce-stationary-comparisons-at-bounds).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem degree_eq (q n : ℤ) : q + (n - q) = n := by omega

private theorem step_homology_image
    {X : Scheme.{u}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (D : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    ∃ h : (D.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology n ⟶
        ((D.H n).step q : AddCommGrpCat.{u + 1}),
      Epi h ∧ h ≫ ((D.H n).step q).arrow =
        HomologicalComplex.homologyMap (D.L.step q).arrow n ≫ (D.c n).hom := by
  let f := HomologicalComplex.homologyMap (D.L.step q).arrow n
  have he : (D.H n).step q = imageSubobject (f ≫ (D.c n).hom) := by
    rw [D.H_formula, Subobject.exists_obj_eq_imageSubobject]
    rw [← imageSubobject_comp_of_epi (factorThruImageSubobject f)]
    rw [← Category.assoc, imageSubobject_arrow_comp]
  let h := factorThruImageSubobject (f ≫ (D.c n).hom) ≫
    (Subobject.isoOfEq _ _ he.symm).hom
  refine ⟨h, inferInstance, ?_⟩
  dsimp only [h]
  simp only [Category.assoc, Subobject.isoOfEq, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  rfl

private theorem stationary_cycle_comparison
    {X : Scheme.{u}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (D : EtaleTermwiseHypercohomology X K) (q p n r : ℤ) (hn : q + p = n)
    (hr : 1 ≤ r)
    (hR : D.L.complexStep (q + r) (n + 1) = ⊥ ∧
      D.L.complexStep (q - r + 1) (n - 1) = ⊤)
    (h : (D.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology n ⟶
      ((D.H n).step q : AddCommGrpCat.{u + 1}))
    [Epi h]
    (hh : h ≫ ((D.H n).step q).arrow =
      HomologicalComplex.homologyMap (D.L.step q).arrow n ≫ (D.c n).hom) :
    ∃ (a : cokernel (Subobject.ofLE _ _
          (filteredComplex_boundaries_le_cycles D.sectionsTotal D.L q n r)) ≅
        (D.H n).gradedPiece q)
      (z : (D.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).cycles n ⟶
        (D.L.complexCycles q n r : AddCommGrpCat.{u + 1})),
      Epi z ∧
      z ≫ (D.L.complexCycles q n r).arrow =
        (D.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles n ≫
          (D.L.complexQuotientπ q (q + 1) (by omega)).f n ∧
      z ≫ cokernel.π (Subobject.ofLE _ _
          (filteredComplex_boundaries_le_cycles D.sectionsTotal D.L q n r)) ≫ a.hom =
        (D.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homologyπ n ≫ h ≫
          cokernel.π (Subobject.ofLE ((D.H n).step (q + 1)) ((D.H n).step q)
            ((D.H n).antitone_step (Int.le_add_one le_rfl))) := by
  classical
  subst n
  have images := fun i => step_homology_image D i (q + p)
  choose a hepi ha using images
  have comp := filteredStationary_cycle_comparison D.sectionsTotal D.L q p r hr
  obtain ⟨z, e, hz_epi, hz, he⟩ := comp hR.1 hR.2 (D.c (q + p)) (D.H (q + p)) a ha hepi
  have haq : a q = h := by
    apply (cancel_mono ((D.H (q + p)).step q).arrow).1
    exact (ha q).trans hh.symm
  refine ⟨e, z, hz_epi, hz, ?_⟩
  simpa only [filteredComplexPageπ, haq] using he

-- Elaborate the dependent presentation, page-realization and comparison families together.
set_option linter.unusedVariables false in
-- The existing hR and ht binders in the signature are used only implicitly.
/-- Stationary comparison naturality whenever the two outer filtration steps stabilize.
There is no support assumption, first-page formula, augmentation, or inverse-image lift.
Source: Stacks Project, Tag 012K, formulas for cycles, boundaries and graded cohomology;
explicit outer-step version of steps 4--5 of lem-weil-pbc-supported-ce-filtered-totals.
(blueprint: lem-weil-pbc-ce-stationary-comparisons-at-bounds).

Proof. Replace the outer steps in the cycle and boundary formulas by bottom and top.
The resulting quotient is the quotient of actual cycles in step q by cycles in step
q+1 and total boundaries lying in step q. Map it to the successive quotient of the
cohomology images of the two steps. Its kernel is exactly those cycles and boundaries,
and it is surjective, yielding the canonical quotient-to-image isomorphism. Transport
it along D.c n and use D.H_formula, then compose with e. This constructs eInf from
representative equations, not an arbitrary isomorphism; proof irrelevance identifies
all witnesses of the outer equalities.
For a filtered total map b, restrict its homology map to each cohomology image and
transport along the c-isomorphisms, obtaining t and ht. Inclusion compatibility
follows by cancelling the target step arrow. The page-map representative hypothesis
and the canonical comparison send each actual cycle to the same image under b.
The projections from actual cycles onto stationary page quotients are epimorphic;
cancel them to prove the cokernel.map equation. Proof irrelevance removes the choice
of hc. Zero totals and zero steps use the same quotient universal properties. -/
theorem exists_etaleCE_stationary_comparisons_at_bounds
    (D : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      EtaleTermwiseHypercohomology X K)
    (e : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      EtaleCEQuotientRealization (D X K)) :
    ∃ (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
          (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
      ∀ {X Y : Scheme.{u}}
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (b : (D X K).sectionsTotal ⟶ (D Y L).sectionsTotal)
        (N : (D X K).sequence ⟶ (D Y L).sequence),
        (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ) ⟶
            ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ),
          s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) →
        EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L) b N →
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  b n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
            (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤)
          (hY : (D Y L).L.complexStep (q + r) (n + 1) = ⊥ ∧
            (D Y L).L.complexStep (q - r + 1) (n - 1) = ⊤),
            (N.hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q) := by
  classical
  have himg := fun X K q n => step_homology_image (D X K) q n
  choose h hepi hh using himg
  have comparisons := fun X K q n r hr hR =>
    @stationary_cycle_comparison X K (D X K) q (n - q) n r
      (degree_eq q n) hr hR
      (h X K q n) (hepi X K q n) (hh X K q n)
  choose a z zepi hz ha using comparisons
  let aPage (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q p n r : ℤ) (hr : 1 ≤ r) (hn : q + p = n)
      (hR : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
        (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤) :
      filteredComplexPageObject (D X K).sectionsTotal (D X K).L r (q, p) ≅
        ((D X K).H n).gradedPiece q := by
    subst n
    exact a X K q (q + p) r hr hR
  refine ⟨fun X K q n r hr hR => e X K q (n - q) r hr ≪≫
    aPage X K q (n - q) n r hr (degree_eq q n) hR, ?_⟩
  intro X Y K L b N hb hN n
  choose s hs using hb
  let bH := ((D X K).c n).inv ≫
    HomologicalComplex.homologyMap b n ≫ ((D Y L).c n).hom
  have hw (q : ℤ) :
      HomologicalComplex.homologyMap (s q) n ≫ h Y L q n ≫
        (((D Y L).H n).step q).arrow =
      h X K q n ≫ (((D X K).H n).step q).arrow ≫ bH := by
    rw [hh]
    dsimp only [bH]
    rw [← Category.assoc (h X K q n), hh]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp only [← Category.assoc]
    rw [← HomologicalComplex.homologyMap_comp, hs,
      HomologicalComplex.homologyMap_comp]
  have hk (q : ℤ) : kernel.ι (h X K q n) ≫
      (HomologicalComplex.homologyMap (s q) n ≫ h Y L q n) = 0 := by
    apply (cancel_mono (((D Y L).H n).step q).arrow).1
    simp only [Category.assoc, hw, zero_comp]
    simp only [← Category.assoc, kernel.condition, zero_comp]
  let t (q : ℤ) := Abelian.epiDesc (h X K q n)
    (HomologicalComplex.homologyMap (s q) n ≫ h Y L q n) (hk q)
  have ht (q : ℤ) : t q ≫ (((D Y L).H n).step q).arrow =
      (((D X K).H n).step q).arrow ≫ bH := by
    apply (cancel_epi (h X K q n)).1
    simpa only [← Category.assoc, t, Abelian.comp_epiDesc] using hw q
  refine ⟨t, ht, ?_⟩
  intro hc q r hr hX hY
  suffices hnat : ∀ (p : ℤ) (hn : q + p = n)
      (hX : (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
        (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤)
      (hY : (D Y L).L.complexStep (q + r) (n + 1) = ⊥ ∧
        (D Y L).L.complexStep (q - r + 1) (n - 1) = ⊤),
      (N.hom r hr).f (q, p) ≫
          (e Y L q p r hr ≪≫ aPage Y L q p n r hr hn hY).hom =
        (e X K q p r hr ≪≫ aPage X K q p n r hr hn hX).hom ≫
          cokernel.map
            (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
              (((D X K).H n).antitone_step (Int.le_add_one le_rfl)))
            (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
              (((D Y L).H n).antitone_step (Int.le_add_one le_rfl)))
            (t (q + 1)) (t q) (hc q) by
    exact hnat (n - q) (degree_eq q n) hX hY
  clear hX hY
  intro p hn hX hY
  subst n
  have : Epi (z X K q (q + p) r hr hX) := zepi X K q (q + p) r hr hX
  have : Epi (cokernel.π (Subobject.ofLE _ _
      (filteredComplex_boundaries_le_cycles (D X K).sectionsTotal (D X K).L q (q + p) r))) :=
    inferInstance
  have hrep := hN
    (((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).cycles (q + p))
    q p r hr
  have hxs :
      ((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles (q + p) ≫
        ((D X K).L.step q).arrow.f (q + p) ≫ b.f (q + p) =
      (HomologicalComplex.cyclesMap (s q) (q + p) ≫
        ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles (q + p)) ≫
          ((D Y L).L.step q).arrow.f (q + p) := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, ← hs,
      HomologicalComplex.comp_f, ← Category.assoc,
      ← HomologicalComplex.cyclesMap_i, Category.assoc]
  have hzY :
      (HomologicalComplex.cyclesMap (s q) (q + p) ≫ z Y L q (q + p) r hr hY) ≫
        ((D Y L).L.complexCycles q (q + p) r).arrow =
      (HomologicalComplex.cyclesMap (s q) (q + p) ≫
        ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles (q + p)) ≫
          ((D Y L).L.complexQuotientπ q (q + 1) (by omega)).f (q + p) := by
    simp only [Category.assoc, hz]
  have hpage := hrep
    (((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles (q + p))
    (HomologicalComplex.cyclesMap (s q) (q + p) ≫
      ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).iCycles (q + p))
    (z X K q (q + p) r hr hX)
    (HomologicalComplex.cyclesMap (s q) (q + p) ≫ z Y L q (q + p) r hr hY)
    hxs (hz X K q (q + p) r hr hX) hzY
  dsimp only [filteredComplexPageπ] at hpage
  dsimp only [Iso.trans_hom]
  dsimp only [aPage, filteredComplexPageObject]
  apply (cancel_epi (e X K q p r hr).inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles (D X K).sectionsTotal (D X K).L q (q + p) r)))).1
  apply (cancel_epi (z X K q (q + p) r hr hX)).1
  simp only [Category.assoc]
  have hpage' := congrArg
    (fun f => f ≫ (e Y L q p r hr).hom ≫ (a Y L q (q + p) r hr hY).hom) hpage
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hpage'
  rw [hpage']
  rw [ha]
  rw [reassoc_of% (ha X K q (q + p) r hr hX)]
  rw [← HomologicalComplex.homologyπ_naturality_assoc]
  have hdesc : h X K q (q + p) ≫ t q =
      HomologicalComplex.homologyMap (s q) (q + p) ≫ h Y L q (q + p) :=
    Abelian.comp_epiDesc _ _ _
  rw [cokernel.π_desc, ← reassoc_of% hdesc]

end AlgebraicGeometry.Etale
