/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCERowOrdinaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleCECanonicalRowComparison
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology

import WeilConjectures.CategoryTheory.CartanEilenbergSecondFiltration
import WeilConjectures.CategoryTheory.CartanEilenbergTotalResolution
import all WeilConjectures.CategoryTheory.SecondFiltrationRowCohomology
import all WeilConjectures.CategoryTheory.SecondFiltrationSignedFirstPage
import all WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Algebra.Homology.KInjectiveResolution

/-! # Prescribed normalized CE presentations

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-normalized-row-presentations).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_coefficient_naturality
    (X : Scheme.{uNatural})
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}}
    (v : G ⟶ G') (R : InjectiveResolution G) (R' : InjectiveResolution G')
    (φ : R.Hom R' v) (p : ℕ) :
    HomologicalComplex.homologyMap
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ.hom) p ≫ (ceRowOrdinaryIso X G' R' p).hom =
      (ceRowOrdinaryIso X G R p).hom ≫ AddCommGrpCat.ofHom (Sheaf.H.map v p) := by
  have he : (Sheaf.functorH.{uNatural + 1} X.smallEtaleTopology p).map v ≫
      R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom =
    R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
      AddCommGrpCat.ofHom (EtaleComparisonAux.postClass φ.hom' (p : ℤ)) := by
    ext a
    exact (EtaleComparisonAux.extClass_naturality v _ _ φ p a).symm
  have hc := Scheme.classSectionsIso_naturality X φ.hom' (p : ℤ)
  have hnat : AddCommGrpCat.ofHom (Sheaf.H.map v p) ≫
      (ceRowOrdinaryIso X G' R' p).inv =
    (ceRowOrdinaryIso X G R p).inv ≫ HomologicalComplex.homologyMap
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map φ.hom) p := by
    dsimp only [ceRowOrdinaryIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
    simp only [Category.assoc, HomologicalComplex.homologyFunctor_map]
    erw [reassoc_of% he]
    have hc' : AddCommGrpCat.ofHom (EtaleComparisonAux.postClass φ.hom' (p : ℤ)) ≫
        (SheafPullbackResolution.classSectionsIso X R'.cochainComplex (p : ℤ)).hom =
      (SheafPullbackResolution.classSectionsIso X R.cochainComplex (p : ℤ)).hom ≫
        HomologicalComplex.homologyMap
          (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ.hom') (p : ℤ) := by
      exact hc
    erw [reassoc_of% hc']
    let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
    have h : (F.mapHomologicalComplex _).map φ.hom' ≫
        (R'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom =
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ.hom)
          ComplexShape.embeddingUpNat := by
      apply HomologicalComplex.hom_f_injective
      funext i
      exact HomologicalComplex.mapExtensIso_hom_f_naturality
        φ.hom ComplexShape.embeddingUpNat F i
    rw [← HomologicalComplex.homologyMap_comp_assoc, h,
      HomologicalComplex.homologyMap_comp_assoc]
    erw [HomologicalComplex.extendHomologyIso_hom_naturality
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
      ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) (hj' := rfl)]
  apply (cancel_mono (ceRowOrdinaryIso X G' R' p).inv).1
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun t ↦ (ceRowOrdinaryIso X G R p).hom ≫ t) hnat.symm

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent CE and normalized page data together.
/-- Construct normalized presentations and pin their first-page comparison to the
concrete signed row comparison. No scheme-map naturality is asserted here.
Source: Stacks Project, Tags 015J, 015K, 012K and 06XR.
(blueprint: lem-weil-pbc-ce-normalized-row-presentations).

Proof. Apply exists_hypercohomology_firstPage to each prescribed augmented bicomplex,
retaining I, a, the second filtration and the pinned total augmentation. Use the
canonical K-injective resolution of K and compose the total-homology comparison with
resolutionEtaleCohomologyIso; transport the finite homology-image filtration by this
composite. Build every positive page from filteredComplex_page_differential_exists_unique
and every successor comparison from filteredComplex_normalized_homology. Adjoin the
page-zero graded complex via filteredComplex_graded_homology. Its negative row terms
vanish by extension by zero. The canonical rowComparison identifies the first page
with row homology. Multiply it by (-1)^(pq), and compose with the inverse of the
row resolution isoRightDerivedObj to define eDerived. Define ordinaryComparison as
isoRightDerivedObj followed by ceRowOrdinaryIso. Their intermediate maps cancel,
giving the displayed equation. The signed d1 equation and right-derived naturality
give dDerived; the explicit Ext/sections comparison is natural for coefficient maps,
giving ordinary_naturality. Assemble these witnesses as EtaleTermwiseHypercohomology.
Every positive page is the concrete boundary cokernel, so j is the identity comparison
and successor normalization holds. The construction works at p=0, for zero rows,
negative complex degrees and empty diagonals using the same quotient universal
properties. -/
theorem exists_etaleCE_normalized_row_presentations
    (I : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
        (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ((CochainComplex.single₀
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj K.obj ⟶ I X K)
    (hbelow : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s))
    (hrows : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ), QuasiIso ((a X K).f s))
    (hterms : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ), Injective (((I X K).X s).X r))
    (hhorizontal : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ) (r : ℕ),
      Injective (((I X K).cycles s).X r) ∧
      Injective ((image ((I X K).d (s - 1) s)).X r) ∧
      Injective (((I X K).homology s).X r))
    (hquasi : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
      (s : ℤ),
      QuasiIso (HomologicalComplex.cyclesMap (a X K) s) ∧
      QuasiIso (image.map (Arrow.homMk' ((a X K).f (s - 1)) ((a X K).f s)
        ((a X K).comm (s - 1) s))) ∧
      QuasiIso (HomologicalComplex.homologyMap (a X K) s)) :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (δ : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r),
        FilteredComplexPageDifferential (P X K).sectionsTotal (P X K).L r)
      (j : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r), (P X K).sequence.page r hr ≅ (δ X K r hr).page),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        (P X K).I = I X K) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
        FilteredComplexHomologyNormalized (P X K).sectionsTotal (P X K).L r (δ X K r hr) pq
          ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
            (ComplexShape.up' (r, 1 - r)) pq).mapIso (j X K r hr).symm ≪≫
            (P X K).sequence.iso r (r + 1) pq rfl hr ≪≫
            (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
              (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
                (j X K (r + 1) (by omega)))) ∧
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (p : ℕ) (q : ℤ),
        (j X K 1 (by omega)).inv.f (q, (p : ℤ)) ≫ ((P X K).firstPageIso p q).hom =
          ((P X K).signedRowComparison p q).hom ≫
            (ceRowOrdinaryIso X (K.obj.X q) (cePresentationRow (P X K) q) p).hom) := by
  classical
  have pointwise (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})) :
      ∃ (D : EtaleTermwiseHypercohomology X K)
        (δ : ∀ (r : ℤ) (hr : 1 ≤ r),
          FilteredComplexPageDifferential D.sectionsTotal D.L r)
        (j : ∀ (r : ℤ) (hr : 1 ≤ r), D.sequence.page r hr ≅ (δ r hr).page),
        D.I = I X K ∧
        (∀ (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ),
          FilteredComplexHomologyNormalized D.sectionsTotal D.L r (δ r hr) pq
            ((HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
              (ComplexShape.up' (r, 1 - r)) pq).mapIso (j r hr).symm ≪≫
              D.sequence.iso r (r + 1) pq rfl hr ≪≫
              (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
                (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
                  (j (r + 1) (by omega)))) ∧
        (∀ (p : ℕ) (q : ℤ),
          (j 1 (by omega)).inv.f (q, (p : ℤ)) ≫ (D.firstPageIso p q).hom =
            (D.signedRowComparison p q).hom ≫
              (ceRowOrdinaryIso X (K.obj.X q) (cePresentationRow D q) p).hom) := by
    let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
    let J := I X K
    let T := (((CartanEilenbergPresentation.mappedFunctor F).obj J).flip).total
      (ComplexShape.up ℤ)
    obtain ⟨L, Eold, e₀, e₁, hL, hd₀, hpages, hd₁, hneg, habut⟩ :=
      Functor.cartanEilenberg_second_filtration F K J (a X K) (hbelow X K)
        (hterms X K) (hrows X K)
    let δ (r : ℤ) (hr : 1 ≤ r) : FilteredComplexPageDifferential T L r :=
      (filteredComplex_page_differential_exists_unique T L r hr).choose
    have h01 : ∀ pq : ℤ × ℤ,
        Nonempty ((Eold.page 0 (by decide)).homology pq ≅ (δ 1 (by omega)).page.X pq) := by
      rintro ⟨p, q⟩
      obtain ⟨hBZ, ⟨eQ⟩⟩ := filteredComplex_graded_homology T L (Eold.page 0 (by decide)) e₀ hd₀ p q
      exact ⟨eQ⟩
    let pages (r : ℤ) (hr : 0 ≤ r) :=
      if h : r = 0 then h ▸ Eold.page 0 (by decide) else (δ r (by omega)).page
    have page_eq (r : ℤ) (hr : 1 ≤ r) :
        pages r (by omega) = (δ r hr).page := by
      have hr0 : r ≠ 0 := by omega
      simp only [pages, dite_eq_right hr0]
    let jp (r : ℤ) (hr : 1 ≤ r) : pages r (by omega) ≅ (δ r hr).page :=
      eqToIso (page_eq r hr)
    let E : CohomologicalSpectralSequence AddCommGrpCat.{uNatural + 1} 0 :=
      { page := pages
        iso := by
          intro r r' pq hrr' hr
          subst r'
          by_cases h : r = 0
          · subst r
            simpa [pages] using (h01 pq).some
          · have hr1 : 1 ≤ r := by omega
            let eH := (filteredComplex_normalized_homology T L r hr1 (δ r hr1) pq).choose
            exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
                (ComplexShape.up' (r, 1 - r)) pq).mapIso (jp r hr1) ≪≫ eH ≪≫
              (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
                (ComplexShape.up' (r + 1, 1 - (r + 1))) pq).mapIso
                  (jp (r + 1) (by omega)).symm }
    let R : ∀ q : ℤ, InjectiveResolution (K.obj.X q) := fun q ↦
      { cocomplex := J.X q
        injective := hterms X K q
        ι := (a X K).f q
        quasiIso := hrows X K q }
    let eRow := (Functor.secondFiltration_row_cycle_comparison F J (hbelow X K) L hL).choose
    let eSigned := fun (p : ℕ) (q : ℤ) ↦ ((p : ℤ) * q).negOnePow • eRow p q
    have hdSigned : ∀ (p : ℕ) (q : ℤ),
        (δ 1 (by omega)).page.d (q, (p : ℤ)) (q + 1, (p : ℤ)) ≫
          (eSigned p (q + 1)).hom =
        (eSigned p q).hom ≫ HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (J.d q (q + 1))) p := by
      have hdRow (r : ℕ) (s : ℤ) :
          (δ 1 (by omega)).page.d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫
            (eRow r (s + 1)).hom =
          (r : ℤ).negOnePow • ((eRow r s).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (J.d s (s + 1))) r) := by
        let data := Functor.secondFiltration_row_cycle_comparison F J (hbelow X K) L hL
        let t := data.choose_spec.choose
        let x := data.choose_spec.choose_spec.choose
        have ht := data.choose_spec.choose_spec.choose_spec.1
        have hx := data.choose_spec.choose_spec.choose_spec.2.1
        have he := data.choose_spec.choose_spec.choose_spec.2.2
        change ∀ (r : ℕ) (s : ℤ),
          t r s ≫ (L.step s).arrow.f (s + (r : ℤ)) =
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (J.X s)).iCycles r ≫
              Functor.secondFiltrationRowι F J r s at ht
        change ∀ (r : ℕ) (s : ℤ),
          x r s ≫ (L.complexCycles s (s + (r : ℤ)) 1).arrow =
            t r s ≫ (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)) at hx
        change ∀ (r : ℕ) (s : ℤ),
          x r s ≫ filteredComplexPageπ T L 1 (s, (r : ℤ)) ≫ (eRow r s).hom =
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (J.X s)).homologyπ r at he
        let e := eRow
        let R := fun s : ℤ ↦ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (J.X s)
        let K := (((CartanEilenbergPresentation.mappedFunctor F).obj J).flip).total
          (ComplexShape.up ℤ)
        let f := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (J.d s (s + 1))
        let z := (r : ℤ).negOnePow
        let c := HomologicalComplex.cyclesMap f r
        let π := filteredComplexPageπ K L 1 (s, (r : ℤ))
        have hrep := (δ 1 (by omega)).on_representatives ((R s).cycles r) (s, (r : ℤ))
          (s + 1, (r : ℤ)) (by
            change (s, (r : ℤ)) + (1, 1 - 1) = (s + 1, (r : ℤ))
            ext <;> simp)
          (t r s) (z • (c ≫ t r (s + 1)))
          (x r s) (z • (c ≫ x r (s + 1)))
          (by
            simp only [Linear.units_smul_comp, Category.assoc]
            rw [reassoc_of% (ht r s), ht r (s + 1)]
            exact Functor.row_cycle_total_d F J r s)
          (hx r s)
          (by simp only [Linear.units_smul_comp, Category.assoc, hx r (s + 1)])
        have hπ : Epi (x r s ≫ π) := by
          apply (epi_comp_iff_of_isIso (x r s ≫ π) (e r s).hom).mp
          rw [Category.assoc, he r s]
          infer_instance
        apply (cancel_epi (x r s ≫ π)).1
        change (x r s ≫ π) ≫ (δ 1 (by omega)).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫
            (e r (s + 1)).hom =
          (x r s ≫ π) ≫ (z • ((e r s).hom ≫ HomologicalComplex.homologyMap f r))
        calc
          (x r s ≫ π) ≫ (δ 1 (by omega)).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫
              (e r (s + 1)).hom =
            (z • (c ≫ x r (s + 1))) ≫
              filteredComplexPageπ K L 1 (s + 1, (r : ℤ)) ≫ (e r (s + 1)).hom := by
                simpa only [Category.assoc] using
                  congrArg (fun g ↦ g ≫ (e r (s + 1)).hom) hrep
          _ = z • (c ≫ (R (s + 1)).homologyπ r) := by
            simpa only [Linear.units_smul_comp, Category.assoc] using
              congrArg (fun g ↦ z • (c ≫ g)) (he r (s + 1))
          _ = z • ((R s).homologyπ r ≫ HomologicalComplex.homologyMap f r) := by
            rw [HomologicalComplex.homologyπ_naturality]
          _ = (x r s ≫ π) ≫ (z • ((e r s).hom ≫ HomologicalComplex.homologyMap f r)) := by
            simp only [Linear.comp_units_smul, ← Category.assoc]
            rw [Category.assoc (x r s) π, he r s]
      intro r s
      dsimp only [eSigned, Preadditive.smul_iso_hom]
      rw [Linear.comp_units_smul, hdRow r s, Linear.units_smul_comp, smul_smul,
        show (r : ℤ) * (s + 1) = (r : ℤ) * s + (r : ℤ) by rw [mul_add, mul_one],
        Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
    have ha (q : ℤ) : (R q).ι.f 0 ≫ (J.d q (q + 1)).f 0 =
        K.obj.d q (q + 1) ≫ (R (q + 1)).ι.f 0 := by
      have h := congrArg (fun f ↦ f.f 0) ((a X K).comm q (q + 1))
      simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
        CochainComplex.single₀_map_f_zero] using h
    obtain ⟨aug, haug, hq, hki⟩ :=
      Functor.cartanEilenberg_total_resolution K J (a X K) (hbelow X K)
        (hterms X K) (hrows X K)
    let ρ := CochainComplex.grothendieckKInjectiveResolutionChoice K.obj
    let τ : CochainComplex.KInjectiveResolutionChoice K.obj := ⟨_, aug, hq, hki⟩
    let τR : CochainComplex.KInjectiveResolution K.obj :=
      { I := τ.complex, ι := τ.map, quasiIso_ι := τ.quasiIso, isKInjective := τ.isKInjective }
    let ρR : CochainComplex.KInjectiveResolution K.obj :=
      { I := ρ.complex, ι := ρ.map, quasiIso_ι := ρ.quasiIso, isKInjective := ρ.isKInjective }
    let u : τ.complex ⟶ ρ.complex := (τR.homotopyEquiv ρR).hom
    let v : ρ.complex ⟶ τ.complex := (τR.homotopyEquiv ρR).inv
    have hu : Nonempty (Homotopy (τ.map ≫ u) ρ.map) := ⟨τR.homotopyEquivHomotopy ρR⟩
    have huv : Nonempty (Homotopy (u ≫ v) (𝟙 _)) :=
      ⟨(τR.homotopyEquiv ρR).homotopyHomInvId⟩
    have hvu : Nonempty (Homotopy (v ≫ u) (𝟙 _)) :=
      ⟨(τR.homotopyEquiv ρR).homotopyInvHomId⟩
    let equiv : HomotopyEquiv τ.complex ρ.complex := ⟨u, v, huv.some, hvu.some⟩
    obtain ⟨e, he⟩ := Functor.cartanEilenberg_mapped_total_iso F J (hbelow X K)
    let w := e.hom ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map u
    let c₀ := fun n ↦ (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso e ≪≫
      (F.mapHomotopyEquiv equiv).toHomologyIso n
    let c := fun n ↦ c₀ n ≪≫
      (@resolutionEtaleCohomologyIso.{uNatural} X K.obj ρ.complex ρ.map
        ρ.quasiIso ρ.isKInjective n)
    obtain ⟨H, hfin, hstep, _⟩ := habut _ c
    let D : EtaleTermwiseHypercohomology X K :=
      { I := J
        a := a X K
        below := hbelow X K
        terms := hterms X K
        rows := hrows X K
        horizontal := hhorizontal X K
        horizontal_quasi := hquasi X K
        L := L
        filtration_formula := hL
        E := E
        e₀ := e₀
        d₀ := by simpa [E, pages] using hd₀
        subquotients := by
          intro p q r hr
          refine ⟨filteredComplex_boundaries_le_cycles T L p (p + q) r, ?_⟩
          have hr0 : r ≠ 0 := by omega
          simpa [E, pages, hr0, FilteredComplexPageDifferential.page, filteredComplexPageObject]
            using (show Nonempty ((δ r hr).page.X (p, q) ≅
              filteredComplexPageObject T L r (p, q)) from ⟨Iso.refl _⟩)
        eDerived := fun p q ↦ eSigned p q ≪≫ ((R q).isoRightDerivedObj F p).symm
        dDerived := by
          intro p q
          have hnat := InjectiveResolution.isoRightDerivedObj_inv_naturality
            (K.obj.d q (q + 1)) (R q) (R (q + 1)) (J.d q (q + 1)) (ha q) F p
          change ((R q).isoRightDerivedObj F p).inv ≫
              (F.rightDerived p).map (K.obj.d q (q + 1)) =
            HomologicalComplex.homologyMap
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (J.d q (q + 1))) p ≫
                ((R (q + 1)).isoRightDerivedObj F p).inv at hnat
          dsimp only [Iso.trans_hom, Iso.symm_hom]
          change (δ 1 (by omega)).page.d _ _ ≫ _ = _
          rw [← Category.assoc, hdSigned p q, Category.assoc]
          simpa only [Category.assoc] using
            congrArg (fun f ↦ (eSigned p q).hom ≫ f) hnat.symm
        ordinaryComparison := fun p q ↦ (R q).isoRightDerivedObj F p ≪≫
          ceRowOrdinaryIso X (K.obj.X q) (R q) p
        ordinary_naturality := by
          intro p q
          let φ : (R q).Hom (R (q + 1)) (K.obj.d q (q + 1)) :=
            ⟨J.d q (q + 1), ha q⟩
          have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality
            (K.obj.d q (q + 1)) (R q) (R (q + 1)) φ.hom (ha q) F p
          have hc := ordinary_coefficient_naturality X (K.obj.d q (q + 1))
            (R q) (R (q + 1)) φ p
          dsimp only [Iso.trans_hom]
          simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat
          simp only [Category.assoc]
          rw [reassoc_of% hnat]
          erw [hc]
        negative := by
          intro p q hq
          have hstep : L.complexStep p (p + q) = ⊥ := by
            rw [hL]
            simp [HomologicalComplex₂.secondFiltration,
              Finset.Icc_eq_empty_of_lt (by omega : p + q < p)]
          have hz := Functor.gradedPiece_isZero_of_complexStep_eq_bot L p (p + q) hstep
          have hcycles : IsZero (L.complexCycles p (p + q) 1 : AddCommGrpCat.{uNatural + 1}) :=
            IsZero.of_mono (L.complexCycles p (p + q) 1).arrow hz
          have : Epi (filteredComplexPageπ T L 1 (p, q)) := by
            dsimp [filteredComplexPageπ]
            infer_instance
          have hpage := IsZero.of_epi (filteredComplexPageπ T L 1 (p, q)) hcycles
          simpa [E, pages, FilteredComplexPageDifferential.page] using hpage
        ρ := ρ
        aug := aug
        aug_formula := haug
        comparison := u
        over_K := hu
        w := w
        w_formula := by
          intro m s n h
          dsimp [w]
          rw [← Category.assoc, he m s n h, Category.assoc,
            ← F.map_comp, Category.assoc]
        c := c
        c_formula := by
          intro n
          dsimp only [c, c₀, Iso.trans_hom]
          congr 1
          exact (HomologicalComplex.homologyMap_comp e.hom
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map u) n).symm
        H := H
        finite := hfin
        H_formula := hstep }
    let j : ∀ (r : ℤ) (hr : 1 ≤ r), D.sequence.page r hr ≅ (δ r hr).page := jp
    refine ⟨D, δ, j, rfl, ?_, ?_⟩
    · intro r hr pq
      have hr0 : r ≠ 0 := by omega
      have hn := (filteredComplex_normalized_homology T L r hr (δ r hr) pq).choose_spec.1
      change FilteredComplexHomologyNormalized T L r (δ r hr) pq _
      simpa only [j, EtaleTermwiseHypercohomology.sequence, D, E, dite_eq_right hr0,
        Functor.mapIso_symm, Iso.trans_assoc, Iso.symm_self_id_assoc,
        Iso.symm_self_id, Iso.trans_refl] using hn
    · intro p q
      change (𝟙 _) ≫ ((eSigned p q).hom ≫ ((R q).isoRightDerivedObj F p).inv) ≫
          ((R q).isoRightDerivedObj F p).hom ≫ (ceRowOrdinaryIso X (K.obj.X q) (R q) p).hom =
        (eSigned p q).hom ≫ (ceRowOrdinaryIso X (K.obj.X q) (R q) p).hom
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
  choose P δ j hI hn he using pointwise
  exact ⟨P, δ, j, hI, hn, he⟩

end AlgebraicGeometry.Etale
