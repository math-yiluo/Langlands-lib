import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualReduction
import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationProof
import Langlands.GroupScheme.SimplyConnected.TypeE7KernelCenterMovement
import Langlands.GroupScheme.NormOneCenterAutomorphismOppositeProof

/-! # The local E7 exclusion and the remaining E6 marking -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

/-- The branch-marked actual E6 index with trivial full star action. -/
def HasRankOneE6BranchIndex {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) : Prop :=
  (∃ e : d.Vertex ≃ Fin 6,
    d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) ∧ d.StarIsTrivial

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The E7 branch marking with trivial star is impossible locally for a
simply connected group. -/
theorem not_E7_branch_mark (hsc : IsSimplyConnected G) (e : d.Vertex ≃ Fin 7)
    (h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) : False :=
  HasCentralDivisionNormOnePresentation.not_hasCenterMovingAutomorphism
    normOneCenterAutomorphismOpposite
    (d.anisotropicKernel_divisionModel_of_E7_branch_mark e hsc h hstar) (by decide)
    (d.hasCenterMovingAutomorphism_of_E7_branch_mark e hsc h hstar)

end TitsIndexData

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Actual component realization suffices to reduce the local enumeration
to the E6 branch marking and the higher-B, G2 and D4 residual indices. -/
theorem localRankOneTitsIndex_or_E6_or_residual_of_componentFactor
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (d : TitsIndexData G) (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) :
    ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasRankOneE6BranchIndex ∨ d.HasResidualRankOneIndex := by
  by_cases hE6 : d.HasRankOneE6BranchIndex
  · exact Or.inr (Or.inl hE6)
  · have hcomponents := localAnisotropicCartanComponents_of_componentFactor
      hfactor localAnisotropicTypeA
    have htype := absolutelyAlmostSimpleCartanClassification K G d has
    rcases localRankOneTitsIndex_or_residual_of_typeE_exclusions hcomponents d htype hsc has hrank
        (fun e h hstar => hE6 ⟨⟨e, h⟩, hstar⟩) (d.not_E7_branch_mark hsc) with hindex | hresidual
    · exact Or.inl hindex
    · exact Or.inr (Or.inr hresidual)

end Langlands.GroupScheme
