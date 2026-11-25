/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections

import WeilConjectures.AlgebraicGeometry.EtaleCESupportedFirstPageLifts
import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryComparisonsAtBounds

/-! # Support-controlled filtered CE totals

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-supported-ce-filtered-totals).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem supported_complexStep_antitone
    {X : Scheme.{u}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (D : EtaleTermwiseHypercohomology X K) (n : ℤ) :
    Antitone (fun q ↦ D.L.complexStep q n) := by
  intro a b hab
  have h := imageSubobject_comp_le
    ((Subobject.ofLE (D.L.step b) (D.L.step a) (D.L.antitone_step hab)).f n)
    ((D.L.step a).arrow.f n)
  simpa only [DecreasingFiltration.complexStep, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow] using h

set_option linter.unusedVariables false in
-- Elaborate the dependent presentation, support and stationary-page families together.
/-- Construct support-controlled stationary comparisons for maps of augmented CE totals.
The presentation, page maps and stationary comparisons are chosen simultaneously.
The abutment is the homology map of the specified CE-total map; this assertion does not
compare it with an arbitrary supplied map of K-injective resolutions.
Source: Stacks Project, Tag 015J (first spectral sequence), Tag 015K (filtered
functoriality), and Tag 0EZM (common lower support bound).
(blueprint: lem-weil-pbc-supported-ce-filtered-totals).

Proof:
1. For a complex whose terms are all zero choose the zero CE resolution. Otherwise,
   boundedness below gives a least degree b with a nonzero term. Shift b to zero,
   apply exists_cartanEilenberg_resolution, and shift back. The resulting CE rows
   vanish below b, hence below every lower bound a of the original complex. Construct
   the CE presentation from these resolutions, with the canonical augmentation,
   K-injective comparison, finite-diagonal sections comparison and transported
   cohomology-image filtration. In the zero case all these are the zero comparisons.
2. Extend resolution degree by zero, flip, and filter by original complex degree.
   The total in degree i has summands indexed by s+m=i with m nonnegative.
   Thus its step p is zero for p>i and is the whole total for p<=a, for every
   lower support bound a of K. Construct the pages from the actual cycle/boundary
   quotients, using common finite crops in the finitely many degrees involved.
   The representative equations identify successive crops and fix the differential
   and page-homology comparison. Apply the signed row identifications and the
   natural ordinary sheaf cohomology comparison to obtain firstPageIso.
3. Exact inverse image and the augmented CE comparison give a bidegree-preserving
   lift of v. Extend, flip and totalize it to obtain u. The augmentation equation
   follows on each degree-zero resolution summand and then by joint epimorphy.
   The sections unit and totalSectionsIso give the sections-total map displayed
   in ht. It preserves every filtration step. Its maps on cycle representatives
   descend to maps of the chosen quotient pages and commute with their homology
   comparisons, giving M. On the first page the row comparison computes precisely
   cohomologyMap followed by Sheaf.H.map(v.f q); the equal sign corrections cancel.
4. If r>=max(1,q-a+2,n-q+2), then q+r>n+1 and q-r+1<=a.
   Hence the two outer filtration steps in degrees n+1 and n-1 are respectively
   zero and the whole object. The stationary cycle/boundary formulas and
   stableSubquotient_at_bounds identify the page with the graded cohomology image.
   Use its canonical quotient-to-image comparison and transport it by c n, rather
   than choosing an arbitrary isomorphism. Its definition uses q,n,r and the two
   outer-step equalities; proof irrelevance removes dependence on the witness a.
   This supplies eInf for the existential support-admissibility condition.
5. Restrict homology of the sections-total map to the cohomology images of the
   filtration steps and transport by c_X and c_Y. These are t, with equation ht.
   On a cycle representative both its stationary page map and the induced image
   map send the class of z to the class of its image under the same total map.
   The representative projections are epimorphic. Cancel them to obtain the
   displayed equation with cokernel.map, for every proof hc (proof irrelevance).
   No unrelated M or eInf is quantified universally: both come from this one
   filtered construction. Empty schemes, zero complexes, negative total degrees
   and empty diagonals satisfy the same zero-object universal properties.
-/
theorem exists_etaleHypercohomology_supported_ce_filtered_totals :
    ∃ (D : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (D X K).sequence ⟶ (D Y L).sequence)
      (eInf : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (q n r : ℤ) (hr : 1 ≤ r) (hR : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r),
        ((D X K).sequence.page r hr).X (q, n - q) ≅ ((D X K).H n).gradedPiece q),
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
          ∀ n : ℤ,
            ∃ (t : ∀ q : ℤ, (((D X K).H n).step q : AddCommGrpCat.{u + 1}) ⟶
            (((D Y L).H n).step q : AddCommGrpCat.{u + 1}))
          (ht : ∀ q : ℤ, t q ≫ (((D Y L).H n).step q).arrow =
            (((D X K).H n).step q).arrow ≫
              (((D X K).c n).inv ≫
                HomologicalComplex.homologyMap
                  ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫
                    (D Y L).totalSectionsIso.inv) n ≫ ((D Y L).c n).hom)),
          ∀ (hc : ∀ q : ℤ,
            Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))) ≫ t q =
              t (q + 1) ≫
                Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                  (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q)))),
          ∀ (q r : ℤ) (hr : 1 ≤ r) (hX : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r)
          (hY : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (L.obj.X s)) ∧
          max 1 (max (q - a + 2) (n - q + 2)) ≤ r),
            ((M f K L v).hom r hr).f (q, n - q) ≫ (eInf Y L q n r hr hY).hom =
              (eInf X K q n r hr hX).hom ≫
                cokernel.map
                  (Subobject.ofLE (((D X K).H n).step (q + 1)) (((D X K).H n).step q)
                    (((D X K).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (Subobject.ofLE (((D Y L).H n).step (q + 1)) (((D Y L).H n).step q)
                    (((D Y L).H n).antitone_step (Int.le_add_one (le_refl q))))
                  (t (q + 1)) (t q) (hc q)) := by
  obtain ⟨D, M, e, hE, hLift, hSupport⟩ := exists_etaleCE_supported_first_page_lifts
  obtain ⟨eBounds, hStable⟩ := exists_etaleCE_stationary_comparisons_at_bounds D e
  have bounds (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (q n r : ℤ)
      (hR : ∃ a : ℤ, (∀ s : ℤ, s < a → IsZero (K.obj.X s)) ∧
        max 1 (max (q - a + 2) (n - q + 2)) ≤ r) :
      (D X K).L.complexStep (q + r) (n + 1) = ⊥ ∧
        (D X K).L.complexStep (q - r + 1) (n - 1) = ⊤ := by
    obtain ⟨a, ha, hr⟩ := hR
    have hqa : q - a + 2 ≤ r :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hr)
    have hnq : n - q + 2 ≤ r :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hr)
    constructor
    · apply bot_unique
      rw [← (hSupport X K a ha (n + 1)).2]
      exact supported_complexStep_antitone (D X K) (n + 1) (by omega)
    · apply top_unique
      rw [← (hSupport X K a ha (n - 1)).1]
      exact supported_complexStep_antitone (D X K) (n - 1) (by omega)
  let eInf := fun X K q n r hr hR ↦ eBounds X K q n r hr (bounds X K q n r hR)
  refine ⟨D, M, eInf, hE, ?_⟩
  intro X Y f K L v
  obtain ⟨u, hu, hPres, hRep⟩ := hLift f K L v
  refine ⟨u, hu, ?_⟩
  intro n
  obtain ⟨t, ht, hPage⟩ := hStable K L
    ((D X K).totalSectionsIso.hom ≫ ceSectionsLift f u ≫ (D Y L).totalSectionsIso.inv)
    (M f K L v) hPres hRep n
  refine ⟨t, ht, ?_⟩
  intro hc q r hr hX hY
  exact hPage hc q r hr (bounds X K q n r hX) (bounds Y L q n r hY)


end AlgebraicGeometry.Etale
