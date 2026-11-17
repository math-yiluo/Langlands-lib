import Langlands.GroupScheme.Reductive.RelativePinnedExistenceReduction
import Langlands.GroupScheme.Reductive.AffinePinnedFppfExistence

/-! # Natural inner corrections of actual pinned-model comparisons -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open AffinePinnedModel

private theorem locallyInner_innerIso {S : Scheme.{u}} (G : GroupScheme S)
    (c : Over.mk (𝟙 S) ⟶ G.X) : IsFppfLocallyInner (G.innerIso c) := by
  refine ⟨Over.mk (𝟙 S), ?_, ?_, ?_, c, ?_⟩
  · change Flat (𝟙 S)
    infer_instance
  · change Surjective (𝟙 S)
    infer_instance
  · change LocallyOfFinitePresentation (𝟙 S)
    infer_instance
  · intro W a x
    have ha : a = Over.homMk W.hom (by simp) := by
      apply Over.OverMorphism.ext
      simpa using a.w
    rw [ha, AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
    exact (comp_innerIso_hom G c W x).symm

/-- Geometric local pinning and its exact source discrepancy supply the
existence input of the proved uniqueness-and-descent construction. -/
theorem hasFppfLocalPinnedRepresentatives_of_localNormalization
    (h : FppfLocalPinnedNormalizationExistenceStatement.{u}) :
    HasFppfLocalPinnedRepresentatives.{u} := by
  intro M N T f g e
  obtain ⟨U, q, hf, hs, hl, d, c, hd, hc⟩ := h M N f g e
  refine ⟨U, q, hf, hs, hl, d, hd.fppfLocallyPinned, ?_⟩
  change IsFppfLocallyInner (pullComparison e q ≪≫ d.symm)
  rw [← hc]
  exact locallyInner_innerIso _ c

/-- Every actual comparison has an fppf-local pinned representative of its
inner class, over arbitrary common schemes. -/
theorem AffinePinnedModel.hasFppfLocalPinnedRepresentatives :
    HasFppfLocalPinnedRepresentatives.{u} :=
  hasFppfLocalPinnedRepresentatives_of_localNormalization
    fppfLocalPinnedNormalizationExistence

/-- Natural inner corrections of actual comparisons of supplied affine
pinned split reductive models, with all coherence and adjoint-section laws. -/
theorem relativePinnedComparisonExistence : RelativePinnedComparisonExistenceStatement.{u} :=
  relativePinnedComparisonExistence_of_localPinnedRepresentatives
    AffinePinnedModel.hasFppfLocalPinnedRepresentatives

end Langlands.GroupScheme
