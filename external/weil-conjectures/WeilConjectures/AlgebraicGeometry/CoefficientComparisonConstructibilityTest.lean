/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import Mathlib.Algebra.Module.FinitePresentation
/-! # The stratum test for coefficient-sized comparison
Source: blueprint constructible comparison, Stacks Tag 09AK.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Canonical inverse image preserves and reflects constructibility of etale modules.
This is a property test on a given etale module, without an essential-surjectivity
claim or a derived assertion.
Source: blueprint theorem-comparison-constructible-sheaves, equivalence part;
finite-local-system comparison, Stacks Tag 09AK
(auxiliary; not a blueprint node).

Proof: inverse image commutes with restriction to each locally closed stratum by
the comparison base-change mate. An etale finite local trivialization pulls back
to a pro-etale trivialization with the same finite module. Conversely, a finite
pro-etale local system descends uniquely to the etale site: finite presentation
over the Noetherian ring lets its trivializations and transition maps descend
along affine pro-etale presentations to etale finite stages. Fully faithful
comparison on each stratum identifies that descended system with the restriction
of the given etale module. The same finite partition thus witnesses etale
constructibility. Affine-local finite partitions glue on each quasi-compact affine
open, and arbitrary schemes are covered by such opens. Constant-scalar restriction
and the coefficient-sized site equivalences preserve covers, the constant finite
models and the stratum inverse images. No quasi-compactness assumption on the
whole scheme is needed. The empty scheme has the empty partition, and the zero
module is covered by the zero finite model, so the two tests also agree there. -/
theorem coefficientComparison_constructibilityTest (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ G : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
      Scheme.IsCoefficientConstructibleEtaleModule X A G ↔
        Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
          ((constructibleComparisonPullback X A).obj G)  := by
  intro G
  have preserves (Y : Scheme.{u}) :
      PreservesFiniteLimits (Scheme.smallModelComparisonInclusion.{u, v} Y) := by
    dsimp [Scheme.smallModelComparisonInclusion]
    have : PreservesFiniteLimits
        (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} Y ⥤ Y.Etale) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.Etale)).inverse)
    have : PreservesFiniteLimits
        (AsSmall.up : Y.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} Y) :=
      inferInstanceAs (PreservesFiniteLimits
        (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.ProEt)).functor)
    infer_instance
  constructor
  · intro h U hU
    obtain ⟨S, hc, hs⟩ := h U hU
    let T : Scheme.Stratification U.toScheme :=
      { n := S.n
        stratum := S.stratum
        isLocallyClosed_stratum := S.isLocallyClosed_stratum
        isConstructible_stratum := hc
        iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
        pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    refine ⟨T, hc, ?_⟩
    intro i V
    have := preserves (S.domain i)
    have hp := coefficient_finite_local_systems_pullback
      (Scheme.smallModelComparisonEtaleTopology.{u, v} (S.domain i))
      (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain i))
      (Scheme.smallModelComparisonInclusion.{u, v} (S.domain i)) A _ (hs i)
    obtain ⟨e⟩ := coefficientComparison_fixedPullback.{u, v} (S.immersion i ≫ U.ι) A
    have ht := coefficientProEtale_finite_iso A (e.app G).symm hp
    obtain ⟨R, hR, hm⟩ := ht V
    refine ⟨R, hR, ?_⟩
    intro W f hf
    obtain ⟨M, hM, he⟩ := hm W f hf
    have := hM
    exact ⟨M, Module.finitePresentation_of_finite A M, he⟩
  · intro h U hU
    obtain ⟨S, hc, hs⟩ := h U hU
    let T : Scheme.FiniteLocallyClosedStratification U.toScheme :=
      { n := S.n
        stratum := S.stratum
        isLocallyClosed_stratum := S.isLocallyClosed_stratum
        iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
        pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    refine ⟨T, hc, ?_⟩
    intro i
    have ht : IsCoefficientModelLocallyConstantFinite
        (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain i)) A
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
          (S.immersion i ≫ U.ι) A).obj
            ((coefficientModelFixedScalars _ A).obj
              ((constructibleComparisonPullback X A).obj G))) := by
      intro V
      obtain ⟨R, hR, hm⟩ := hs i V
      refine ⟨R, hR, ?_⟩
      intro W f hf
      obtain ⟨M, hM, he⟩ := hm W f hf
      have := hM
      exact ⟨M, inferInstance, he⟩
    obtain ⟨e⟩ := coefficientComparison_fixedPullback.{u, v} (S.immersion i ≫ U.ι) A
    exact coefficientComparison_finite_reflect.{u, v} (S.domain i) A _
      (coefficientProEtale_finite_iso A (e.app G) ht)
end AlgebraicGeometry.ProEtale
