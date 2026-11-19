import Langlands.GroupScheme.SimplyConnected.LocalRankOneE7Exclusion
import Langlands.GroupScheme.Reductive.TitsComponentFactorProof
import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyPresentationProof
import Langlands.GroupScheme.Composition.IsotropicCayleyAutomorphismRankProof

/-! # Local rank-one index reduction to the E6, higher B and D4 cases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- With the hypotheses of the local rank-one enumeration, the actual index
is one of its five alternatives or one of the specified E6, higher B or D4
patterns. -/
def LocalRankOneTitsIndexReductionStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → splitRank G = 1 →
      ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
        (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
        (∃ n : ℕ, d.HasRankOneCIndex n) ∨
        d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasRankOneE6BranchIndex ∨ d.HasRankOneHigherBIndex ∨
        d.HasRankOneD4InnerOrNoFixedLeafIndex

/-- Actual component realization and the Cayley rank argument discharge
the component premise and the G2 case of the preceding reduction. -/
theorem localRankOneTitsIndexReduction : LocalRankOneTitsIndexReductionStatement.{u} := by
  intro K _ _ _ _ G _ _ d hsc has hrank
  rcases localRankOneTitsIndex_or_E6_or_residual_of_componentFactor
      semisimpleTitsComponentFactor d hsc has hrank with hindex | hE6 | hresidual
  · exact Or.inl hindex
  · exact Or.inr (Or.inl hE6)
  · rcases hresidual with hB | hG2 | hD4
    · exact Or.inr (Or.inr (Or.inl hB))
    · exact (localRankOne_not_hasG2Index_of_cayleyStructure
        typeG2CayleyPresentation isotropicCayleyAutomorphismRank d hsc has hrank hG2).elim
    · exact Or.inr (Or.inr (Or.inr hD4))

end Langlands.GroupScheme
