/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCEStationaryPageNaturality

import WeilConjectures.CategoryTheory.CartanEilenbergAllLowerBounds
import WeilConjectures.AlgebraicGeometry.EtaleCECoherentPrescribedResolutions
import WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration

/-! # Supported coherent first-page CE lifts

Source: Stacks Project, Tags 015J, 015K and 012K.
(blueprint: lem-weil-pbc-ce-supported-first-page-lifts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- The map family is indexed by v although its result type does not depend on v.
set_option linter.unusedVariables false in
-- Elaborate the dependent presentation, page-realization and comparison families together.
/-- Construct coherent first-page lifts with filtration bounds for every input support bound.
No stationary comparison or map on the abutment is asserted.
Source: Stacks Project, Tags 015J and 015K; explicit support refinement of the CE
construction in steps 1--3 of lem-weil-pbc-supported-ce-filtered-totals.
(blueprint: lem-weil-pbc-ce-supported-first-page-lifts).

Proof. Choose boundary and homology resolutions that are zero whenever their
objects are zero. The two prescribed-end horseshoe rows then give zero term
resolutions below every lower support bound of K, using one bicomplex for all bounds.
Construct coherent pages and comparisons on these prescribed resolutions.
Extend resolution degree by zero and flip. All diagonal summands have resolution
index nonnegative, so the second filtration is top at a and bottom at n+1 in degree n.
Use boundedBelow_secondFiltration and the filtration formula for these equalities.
Construct the sequence from its actual cycle/boundary quotients in common finite
crops; overlapping crops agree on representatives. Use signed row comparisons and
the natural ordinary sheaf cohomology comparison for the first-page identifications.
Apply augmented CE comparison to the chosen supported resolutions, then extend, flip,
and totalize its lift. The augmentation square follows on diagonal inclusions.
The sections unit and finite-diagonal comparison preserve complex degree. Hence
this map restricts to the filtration steps, and its maps on graded cycles descend
to the chosen page quotients, giving the representative equation and a sequence map.
The natural row comparison computes the required first-page formula; the equal
source and target signs cancel. The zero construction handles all lower bounds
simultaneously. All steps include empty schemes and empty diagonal sums. -/
theorem exists_etaleCE_supported_first_page_lifts :
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
            b (M f K L v)) ∧
      (∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (a : ℤ), (∀ s : ℤ, s < a → IsZero (K.obj.X s)) →
        ∀ n : ℤ, (D X K).L.complexStep a n = ⊤ ∧
          (D X K).L.complexStep (n + 1) n = ⊥) := by
  classical
  have hraw (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
    exists_cartanEilenberg_resolution_all_lower_bounds
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) K
  choose I a hres using hraw
  have hs := fun X K ↦ (hres X K).1
  have hr := fun X K ↦ (hres X K).2.1
  have ht := fun X K ↦ (hres X K).2.2.1
  have hh := fun X K ↦ (hres X K).2.2.2.1
  have hq := fun X K ↦ (hres X K).2.2.2.2
  have hbelow (X : Scheme.{u})
      (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
      ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((I X K).X s) := by
    obtain ⟨b, hb⟩ := K.property
    have : K.obj.IsStrictlyGE b := hb
    refine ⟨b, ?_⟩
    apply hs X K b
    intro s hsb
    exact K.obj.isZero_of_isStrictlyGE b s hsb
  obtain ⟨D, M, e, hI, hE, hLift⟩ :=
    exists_etaleCE_coherent_prescribed_resolutions I a hbelow hr ht hh hq
  refine ⟨D, M, e, hE, hLift, ?_⟩
  intro X K b hb
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj (D X K).I).flip
  have hzero : ∀ i j : ℤ, i < 0 ∨ j < b → IsZero ((J.X i).X j) := by
    intro i j hij
    rcases hij with hi | hj
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      exact HomologicalComplex.isZero_extend_X _ _ i (by
        intro r
        change (r : ℤ) ≠ i
        omega)
    · change IsZero
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((D X K).I.X j)).extend
          ComplexShape.embeddingUpNat |>.X i)
      have hz : IsZero ((D X K).I.X j) := by
        rw [hI X K]
        exact hs X K b hb j hj
      exact (HomologicalComplex.eval AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) i).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).map_isZero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero hz))
  obtain ⟨L, hL, htop, hbot⟩ := J.boundedBelow_secondFiltration b hzero
  intro n
  constructor
  · rw [(D X K).filtration_formula]
    exact (hL b n).symm.trans (htop n)
  · rw [(D X K).filtration_formula]
    exact (hL (n + 1) n).symm.trans (hbot n)

end AlgebraicGeometry.Etale
