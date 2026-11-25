/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleStratifiedEssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-!
# Classicality of finite stratified module sheaves

Source: Stacks Project, Tags 09AK and 099Y.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The comparison counit is invertible for finite locally constant stratified sheaves.
Source: Stacks Project, Tag 09AK, lemma-compare-constructible, proof of essential image
membership (auxiliary; not a blueprint node).

Proof: on each stratum, transport the finite constant models to slice sites and
use their finite geometric stalks to obtain a lisse pro-etale sheaf. The lisse-origin
comparison supplies an etale preimage on that stratum. Apply classicality gluing
through the given finite stratification, proved by Zariski localization and the
open-closed induction in `comparison_essImage_of_stratification`. Finally full
faithfulness of comparison identifies essential-image membership with invertibility
of the counit. This asserts classicality; constructibility of the etale preimage is
proved separately by reflection on the same strata.
-/
theorem isIso_comparison_counit_of_finite_stratification
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (S : Scheme.Stratification X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k : Fin S.n,
      ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ S.domain k),
        Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage (S.domain k) ∧
          ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
            Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj
              (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F) ≅
                (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app F) := by
  apply (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).isIso_counit_app_iff_mem_essImage.mpr
  apply comparison_essImage_of_stratification Λ S F
  intro k
  let L := ((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F
  have hLC : IsLocallyConstantProEtaleFixedModuleSheaf (S.domain k) Λ L := by
    obtain ⟨I, U, f, hf, h⟩ := finiteModels_over Λ L (hS k)
    exact ⟨I, U, f, hf, fun i ↦ by
      obtain ⟨M, _, he⟩ := h i
      exact ⟨M, he⟩⟩
  obtain ⟨G, _, e⟩ := (proEtale_lisse_origin (S.domain k) Λ).2 L
    ⟨hLC, finite_geometricStalk_of_finite_models Λ L (hS k)⟩
  exact ⟨G, e⟩

end AlgebraicGeometry.ProEtale
