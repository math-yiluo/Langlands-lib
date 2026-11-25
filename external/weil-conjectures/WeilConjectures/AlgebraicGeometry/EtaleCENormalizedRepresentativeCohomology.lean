/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.AlgebraicGeometry.EtaleCENormalizedRowRepresentatives

/-! # Normalized CE cohomology on representatives

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-normalized-representative-cohomology).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
-- Elaborate the dependent normalized page and CE comparison families together.
/-- Prescribed normalized CE presentations compute pullback on individual cycle
representatives. This does not identify any supplied first-page map.
Source: Stacks Project, Tags 015J, 015K, 012K and 06XR.
(blueprint: lem-weil-pbc-ce-normalized-representative-cohomology).

Proof. Extend each nonnegative injective row by zero, flip the bicomplex and
form its finite-diagonal sections total using the given individual lower bound.
Use the second filtration. Construct each positive page as its actual boundary
cokernel, with the unique representative differential, and choose the successor
comparison uniquely by its action on successor cycles. Adjoin the graded page
zero. The first-page row calculation identifies each quotient with the homology
of sections of the corresponding injective row; multiply the row comparison by
(-1)^(pq) to cancel the total differential sign. Compare the augmented row with
the chosen injective resolution of K^q. Evaluation at 1 in the constant integer
sheaf identifies its Hom complex with sections; the Ext comparison gives the
ordinaryComparison, and coefficient naturality gives ordinary_naturality.
Retain the augmentation, K-injective comparison, canonical abutment isomorphism
and transported finite image filtration of exists_hypercohomology_firstPage.
For the displayed local equation, the diagonal summand equation for u identifies
the graded sections map with the sections pullback unit followed by the row map
phi. The augmentation equation for phi identifies its row homology map with
Ext pullback followed by the coefficient map v^q. Evaluation at 1 commutes with
both maps. The two identical signed row factors commute with the additive map
and cancel. Thus representatives related by b have the displayed cohomology
classes. This calculation concerns individual representatives; it does not
assert uniqueness or equality of maps on the quotient first page. Zero rows,
p = 0, empty schemes and empty diagonals use the same cokernel calculation. -/
theorem exists_etaleCE_normalized_representative_cohomology
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
            (j X K 1 (by omega)).inv.f (q, (p : ℤ)) ≫ (D.firstPageIso p q).hom ≫
              AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
                (cohomologyMap f (K.obj.X q) p)) =
          z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
            (j Y L 1 (by omega)).inv.f (q, (p : ℤ)) ≫
              (D'.firstPageIso p q).hom := by
  classical
  obtain ⟨P, δ, j, e, hI, hn, he, hc⟩ :=
    exists_etaleCE_normalized_row_representatives I a hbelow hrows hterms hhorizontal hquasi
  refine ⟨P, δ, j, hI, hn, ?_⟩
  intro X Y f K L v D D' φ hφ u hu b A p q x y z z' hxy hz hz'
  have hrow := ceRowOrdinaryIso_naturality f (K.obj.X q) (L.obj.X q)
    (cePresentationRow D q) (cePresentationRow D' q) (v.f q) (φ.f q) (hφ q) p
  have hrep := hc f K L v φ hφ u hu A p q x y z z' hxy hz hz'
  have hsrc := he X K p q
  have htgt := he Y L p q
  calc
    _ = (z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
        (e X K p q).hom) ≫ (ceRowOrdinaryIso X (K.obj.X q)
          (cePresentationRow D q) p).hom ≫
        AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
          (cohomologyMap f (K.obj.X q) p)) := by
      with_unfolding_all
        simpa only [Category.assoc] using congrArg
          (fun t ↦ z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫ t ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) hsrc
    _ = (z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
        (e X K p q).hom) ≫ HomologicalComplex.homologyMap
          (ceRowSectionsMap f (φ.f q)) p ≫
        (ceRowOrdinaryIso Y (L.obj.X q) (cePresentationRow D' q) p).hom := by
      rw [hrow]
    _ = (z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
        (e Y L p q).hom) ≫
        (ceRowOrdinaryIso Y (L.obj.X q) (cePresentationRow D' q) p).hom := by
      with_unfolding_all
        simpa only [Category.assoc] using congrArg
          (fun t ↦ t ≫ (ceRowOrdinaryIso Y (L.obj.X q) (cePresentationRow D' q) p).hom) hrep
    _ = _ := by
      with_unfolding_all
        simpa only [Category.assoc] using (congrArg
          (fun t ↦ z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫ t)
          htgt).symm

end AlgebraicGeometry.Etale
