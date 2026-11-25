/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryPageNaturality

import WeilConjectures.CategoryTheory.CartanEilenbergAugmentedComparison
import WeilConjectures.AlgebraicGeometry.EtaleCEPrescribedQuotientPageDescent
import WeilConjectures.AlgebraicGeometry.EtaleCETotalizeAugmentedComparison

/-! # Coherent first pages from prescribed Cartan--Eilenberg resolutions

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-coherent-prescribed-resolutions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
-- Elaborate the dependent raw-resolution and presentation families together.
/-- Construct coherent first-page comparisons while retaining the supplied bicomplexes.
Source: Stacks Project, Tags 015J and 015K, and the quotient-page construction of
Tag 012K; step 2 of lem-weil-pbc-ce-supported-first-page-lifts.
(blueprint: lem-weil-pbc-ce-coherent-prescribed-resolutions).

Proof. For each supplied augmented CE resolution, apply global sections, extend the
resolution degree by zero, flip, and filter the total by complex degree. The lower
row bound and nonnegative resolution degree make every diagonal finite. Construct
pages from their actual cycle/boundary quotients in a common finite crop. The page
differentials and successor-page comparisons are fixed by their representative
equations, so increasing a crop preserves them. Use the canonical row cohomology
comparison, multiplied in bidegree (q,p) by (-1)^(pq), and the natural comparison to
ordinary sheaf H for the first-page identifications. The total augmentation,
K-injective comparison, its global sections, and the transported homology-image
filtration supply the other fields of D. Its I field is the supplied I, not a newly
chosen resolution.
For each f and v, augmented CE comparison supplies a bidegree-preserving map between
the prescribed resolutions. Extend, flip and totalize it; the degree-zero
augmentation equations give the displayed strict square on every diagonal summand.
Conjugate its sections lift by the finite-diagonal comparisons. It preserves complex
degree, hence factors through every filtration step. Its maps on graded cycles
preserve boundaries and descend to the chosen page quotients. The representative
equations and common crops make these quotient maps commute with successor-page
homology comparisons, defining M. The same row comparison computes its first-page
map as cohomologyMap followed by Sheaf.H.map; the matching signs cancel. These
constructions include zero bicomplexes, empty diagonals and empty schemes. -/
theorem exists_etaleCE_coherent_prescribed_resolutions
    (I : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      ((CochainComplex.single₀
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj K.obj ⟶ I X K)
    (hbelow : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s))
    (hrows : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (s : ℤ), QuasiIso ((a X K).f s))
    (hterms : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (s : ℤ) (r : ℕ), Injective (((I X K).X s).X r))
    (hhorizontal : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (s : ℤ) (r : ℕ),
      Injective (((I X K).cycles s).X r) ∧
      Injective ((image ((I X K).d (s - 1) s)).X r) ∧
      Injective (((I X K).homology s).X r))
    (hquasi : ∀ (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (s : ℤ),
      QuasiIso (HomologicalComplex.cyclesMap (a X K) s) ∧
      QuasiIso (image.map (Arrow.homMk' ((a X K).f (s - 1)) ((a X K).f s)
        ((a X K).comm (s - 1) s))) ∧
      QuasiIso (HomologicalComplex.homologyMap (a X K) s)):
    ∃ (D : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (e : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleCEQuotientRealization (D X K)),
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        (D X K).I = I X K) ∧
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
          ((D X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))) ∧
      (∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        ∃ u : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (D X K).sheafTotal ⟶ (D Y L).sheafTotal,
          ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (D X K).aug ≫ u = v ≫ (D Y L).aug ∧
          let b := (D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
            (D Y L).totalSectionsIso.inv
          (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ) ⟶
              ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ),
            s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) ∧
          EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L)
            b (M f K L v)) := by
  classical
  obtain ⟨D, e, hI, hpages⟩ :=
    exists_etaleCE_prescribed_quotient_page_descent I a hbelow hrows hterms hhorizontal hquasi
  have hm : ∀ (X Y : Scheme.{u}) (f : Y ⟶ X)
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      ∃ N : (D X K).sequence ⟶ (D Y L).sequence,
        (∀ (p : ℕ) (q : ℤ),
          (N.hom 1).f (q, (p : ℤ)) ≫ ((D Y L).firstPageIso p q).hom =
            ((D X K).firstPageIso p q).hom ≫
              AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
                (cohomologyMap f (K.obj.X q) p))) ∧
        ∃ u : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (D X K).sheafTotal ⟶ (D Y L).sheafTotal,
          ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (D X K).aug ≫ u = v ≫ (D Y L).aug ∧
          let b := (D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
            (D Y L).totalSectionsIso.inv
          (∀ q : ℤ, ∃ s : ((D X K).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ) ⟶
              ((D Y L).L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ),
            s ≫ ((D Y L).L.step q).arrow = ((D X K).L.step q).arrow ≫ b) ∧
          EtaleCEPageMapOnRepresentatives (D X K) (D Y L) (e X K) (e Y L) b N := by
    intro X Y f K L v
    obtain ⟨φ, hφ⟩ := exists_cartanEilenberg_augmented_comparison
      (upperStar AddCommGrpCat.{u + 1} f) K.obj L.obj v
      (D X K).I (D X K).a (D X K).below (D X K).rows (D X K).horizontal_quasi
      (D Y L).I (D Y L).a (D Y L).below (D Y L).rows (D Y L).terms
      (D Y L).horizontal (D Y L).horizontal_quasi
    obtain ⟨u, hsquare, hu, hfiltered⟩ :=
      etaleCE_totalize_augmented_comparison f K L v (D X K) (D Y L) φ hφ
    obtain ⟨N, hfirst, hrep⟩ := hpages f K L v φ hφ u hu hfiltered
    exact ⟨N, hfirst, u, hsquare, hfiltered, hrep⟩
  choose M hM using hm
  refine ⟨D, (fun {X Y} f K L v ↦ M X Y f K L v), e, hI, ?_, ?_⟩
  · intro X Y f K L v p q
    exact (hM X Y f K L v).1 p q
  · intro X Y f K L v
    exact (hM X Y f K L v).2

end AlgebraicGeometry.Etale
