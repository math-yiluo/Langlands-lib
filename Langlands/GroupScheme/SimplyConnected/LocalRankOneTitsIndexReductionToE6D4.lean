import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexReduction
import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualExclusions
import Langlands.GroupScheme.SimplyConnected.TypeBOddQuadraticPresentationProof

/-! # Local rank-one index reduction to E6 and D4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a nonarchimedean local field the actual rank-one index satisfies
one of the five enumeration alternatives or one of the stated E6 and D4
patterns. -/
def LocalRankOneTitsIndexReductionToE6D4Statement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → splitRank G = 1 →
      ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
        (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
        (∃ n : ℕ, d.HasRankOneCIndex n) ∨
        d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasRankOneE6BranchIndex ∨ d.HasRankOneD4InnerOrNoFixedLeafIndex

/-- The actual odd quadratic presentation rules out the higher-B pattern
in the preceding local reduction. -/
theorem localRankOneTitsIndexReductionToE6D4 :
    LocalRankOneTitsIndexReductionToE6D4Statement.{u} := by
  intro K _ _ _ _ G _ _ d hsc has hrank
  rcases localRankOneTitsIndexReduction K G d hsc has hrank with hindex | hE6 | hB | hD4
  · exact Or.inl hindex
  · exact Or.inr (Or.inl hE6)
  · exact (d.not_hasRankOneHigherBIndex_of_oddQuadraticPresentation
      typeBOddQuadraticPresentation hsc has hrank hB).elim
  · exact Or.inr (Or.inr hD4)

end Langlands.GroupScheme
