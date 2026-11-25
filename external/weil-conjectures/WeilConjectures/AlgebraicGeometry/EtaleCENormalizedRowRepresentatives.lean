/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCERowOrdinaryComparison
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.AlgebraicGeometry.EtaleCENormalizedRowPresentations
import WeilConjectures.AlgebraicGeometry.EtaleCERowCyclesNaturality

/-! # Normalized CE pages and signed row representatives

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-normalized-row-representatives).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
-- Elaborate the prescribed presentation, normalized pages and signed row families together.
/-- Prescribed CE presentations with signed comparisons to the actual sections-row homology.
Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-normalized-row-representatives).

Proof. Extend each row by zero and form the flipped finite-diagonal sections total.
Use the second filtration and the canonical boundary cokernels on every positive page;
construct the differential from representatives and use the unique normalized successor
homology isomorphism. Adjoin the graded page zero. The row calculation identifies the
first page with the actual homology of the sections of I^q. Multiply this isomorphism
by (-1)^(pq); the two signed factors commute with every additive row map. Compare each
injective row with the chosen resolution and evaluate Ext cocycles at 1. Use precisely
the composite of the row resolution's isoRightDerivedObj with ceRowOrdinaryIso for
ordinaryComparison; take eDerived to be the signed row comparison followed by the inverse
of isoRightDerivedObj. The intermediate resolution comparisons cancel, giving the
first-page equation. Coefficient naturality yields the ordinary_naturality field.
Retain the augmentation, K-injective comparison, canonical abutment and transported
finite image filtration from exists_hypercohomology_firstPage.
The defining equality for u, on each diagonal summand, identifies its graded sections
map with ceRowSectionsMap f (phi.f q). Project the related filtered representatives x,y
onto that graded row, then onto its homology. The equations for z,z' identify those
projections with the boundary cokernel maps, so composing gives the last equality.
This is purely the row-homology calculation; no identification of the row pullback
with ordinary cohomology pullback is used. Zero rows, empty diagonals, p = 0 and empty
schemes use the same cokernel and finite-sum universal properties. -/
theorem exists_etaleCE_normalized_row_representatives
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
        (r : ℤ) (hr : 1 ≤ r), (P X K).sequence.page r hr ≅ (δ X K r hr).page)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
        (p : ℕ) (q : ℤ),
        filteredComplexPageObject (P X K).sectionsTotal (P X K).L 1 (q, (p : ℤ)) ≅
          (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj ((P X K).I.X q)).homology p),
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
          (e X K p q).hom ≫
            (ceRowOrdinaryIso X (K.obj.X q) (cePresentationRow (P X K) q) p).hom) ∧
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      ∀ (A : AddCommGrpCat.{uNatural + 1}) (p : ℕ) (q : ℤ)
        (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
          (q + (p : ℤ)))
        (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
        (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
        x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
          y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
        z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
          y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
        z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
            (e X K p q).hom ≫ HomologicalComplex.homologyMap
              (ceRowSectionsMap f (φ.f q)) p =
          z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
            (e Y L p q).hom := by
  classical
  obtain ⟨P, δ, j, hI, hn, he⟩ := exists_etaleCE_normalized_row_presentations
    I a hbelow hrows hterms hhorizontal hquasi
  refine ⟨P, δ, j, fun X K p q ↦ (P X K).signedRowComparison p q, hI, hn, he, ?_⟩
  intro X Y f K L v D D' φ hφ u hu b A p q x y z z' hxy hz hz'
  have hc := etaleCE_row_cycles_naturality f K L D D' φ u hu A p q x y z z' hxy hz hz'
  have hsrc := D.rowComparison_projection p q
  have htgt := D'.rowComparison_projection p q
  change z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
    (D.signedRowComparison p q).hom ≫
      HomologicalComplex.homologyMap (ceRowSectionsMap f (φ.f q)) p =
    z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
      (D'.signedRowComparison p q).hom
  dsimp only [EtaleTermwiseHypercohomology.signedRowComparison, Preadditive.smul_iso_hom]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp]
  congr 1
  calc
    _ = (z ≫ (D.rowCyclesIso p q).inv) ≫
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (D.I.X q)).homologyπ p ≫
        HomologicalComplex.homologyMap (ceRowSectionsMap f (φ.f q)) p := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ z ≫ t ≫ HomologicalComplex.homologyMap (ceRowSectionsMap f (φ.f q)) p)
        hsrc
    _ = (z ≫ (D.rowCyclesIso p q).inv ≫
        HomologicalComplex.cyclesMap (ceRowSectionsMap f (φ.f q)) p) ≫
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (D'.I.X q)).homologyπ p := by
      rw [HomologicalComplex.homologyπ_naturality]
      simp only [Category.assoc]
    _ = (z' ≫ (D'.rowCyclesIso p q).inv) ≫
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (D'.I.X q)).homologyπ p := by rw [hc]
    _ = _ := by
      simpa only [Category.assoc] using (congrArg (fun t ↦ z' ≫ t) htgt).symm

end AlgebraicGeometry.Etale
