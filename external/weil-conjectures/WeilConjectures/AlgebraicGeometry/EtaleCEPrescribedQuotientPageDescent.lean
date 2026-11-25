/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryPageNaturality
import WeilConjectures.AlgebraicGeometry.EtaleCEPrescribedNormalizedFirstPages
import WeilConjectures.CategoryTheory.FilteredCanonicalPageDescent
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ExtPullbackResolutionSections
import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import WeilConjectures.CategoryTheory.FilteredComplexNormalizedHomology
import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.HypercohomologyFirstPage

/-! # Quotient-page descent on prescribed CE resolutions

Source: Stacks Project, Derived Categories, Tags 015J and 015K; Homology, Tag 012K.
(blueprint: lem-weil-pbc-ce-prescribed-quotient-page-descent).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
-- Elaborate the dependent CE totals and representative equations together.
/-- Retain prescribed CE bicomplexes in quotient-page presentations and descend supplied
filtered augmented comparisons. No bicomplex comparison or total lift is constructed.
Source: Stacks Project, Tag 015J, first-page computation; Tag 015K; Homology,
Tag 012K, lemma-spectral-sequence-filtered-complex and lemma-functorial.
(blueprint: lem-weil-pbc-ce-prescribed-quotient-page-descent).

Proof. For each supplied I,a, use the flipped sections total and complex-degree
filtration. The lower bound for I and extension by zero in the resolution degree
make its diagonal sums finite. Keep I as the I field and a as the augmentation
field of the presentation. Construct positive pages from the actual cycle/boundary
cokernels with the uniquely specified
representative differential. Use the unique normalized successor homology comparison,
specified on successor cycles, for the successor-page isomorphisms. These constructions
are componentwise and require no uniform upper bound on the filtration across all total
degrees. Adjoin the graded page zero. The finite-diagonal row comparison,
multiplied by (-1)^(pq), identifies page one with ordinary sheaf cohomology. Retain the
CE total augmentation, K-injective comparison and transported homology-image filtration
from the first hypercohomology construction to fill every field of D.
Given φ,u and their summand equation, the assumed filtration restrictions carry each
r-cycle to an r-cycle and each r-boundary to an r-boundary. Descend the resulting
maps through the boundary cokernels. The chain-map equation for the total map proves
commutation with the representative differential. The successor homology comparison
is fixed on representatives, so these page maps commute with it and define N.
The cokernel descent equation is precisely EtaleCEPageMapOnRepresentatives.
On page one the summand equation gives the Γ-image of φ in each resolution row,
preceded by the sections pullback unit. Compare each prescribed injective row with
the chosen injective resolution.
Use the Ext-to-resolution-sections comparison, given by evaluation at 1 in the
constant integer sheaf, to choose ordinaryComparison coherently across schemes.
The augmentation equation hφ and the resolution computation of Ext pullback
identify the row map with cohomologyMap followed by Sheaf.H.map.
The identical factors (-1)^(pq) in source and target commute with the additive row
map and cancel, proving the stated first-page equation. All these constructions use
finite limits and cokernels in each bidegree, so zero rows and empty schemes require
no exceptions. -/
theorem exists_etaleCE_prescribed_quotient_page_descent
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
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        (P X K).I = I X K) ∧
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
      (∀ q : ℤ, ∃ s : (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ) ⟶
          (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ),
        s ≫ (D'.L.step q).arrow = (D.L.step q).arrow ≫ b) →
      ∃ N : D.sequence ⟶ D'.sequence,
        (∀ (p : ℕ) (q : ℤ),
        (N.hom 1).f (q, (p : ℤ)) ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
        EtaleCEPageMapOnRepresentatives D D' (e X K) (e Y L) b N := by
  classical
  obtain ⟨P, δ, j, hI, hj, hfirst⟩ :=
    exists_etaleCE_prescribed_normalized_first_pages I a hbelow hrows hterms
      hhorizontal hquasi
  let e : ∀ (X : Scheme.{uNatural})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
      EtaleCEQuotientRealization (P X K) :=
    fun X K q p r hr ↦
      (HomologicalComplex.eval AddCommGrpCat.{uNatural + 1}
        (ComplexShape.up' (r, 1 - r)) (q, p)).mapIso (j X K r hr)
  refine ⟨P, e, hI, ?_⟩
  intro X Y f K L v
  dsimp only
  intro φ hφ u hu hb
  obtain ⟨N, hN⟩ := exists_filteredCanonical_page_descent
    (P X K).sectionsTotal (P Y L).sectionsTotal (P X K).L (P Y L).L
    (P X K).sequence (P Y L).sequence (δ X K) (δ Y L) (j X K) (j Y L)
    (hj X K) (hj Y L)
    ((P X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫ (P Y L).totalSectionsIso.inv) hb
  refine ⟨N, ?_, ?_⟩
  · apply hfirst f K L v φ hφ u hu hb (N.hom 1)
    intro A q p x y z z' hxy hz hz'
    exact hN A q p 1 (by omega) x y z z' hxy hz hz'
  · exact hN

end AlgebraicGeometry.Etale
