import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualReduction
import Langlands.GroupScheme.SimplyConnected.TypeBOddQuadraticPresentationStatement

/-! # Removing the higher-B residual under the general quadratic presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The concrete G2 or inner-or-no-fixed-leaf D4 patterns left after the
higher-B residual is removed. -/
def TitsIndexData.HasExceptionalResidualRankOneIndex
    {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (d : TitsIndexData H) : Prop :=
  d.HasRankOneG2Index ∨ d.HasRankOneD4InnerOrNoFixedLeafIndex

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The general type-B presentation excludes the concrete higher-B residual
for actual local simply connected absolutely almost-simple rank-one groups. -/
theorem TitsIndexData.not_hasRankOneHigherBIndex_of_oddQuadraticPresentation
    (d : TitsIndexData G)
    (hpresentation : TypeBOddQuadraticPresentationStatement.{u})
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) :
    ¬ d.HasRankOneHigherBIndex := by
  rintro ⟨n, hn, ⟨e, j, _, hnumbering⟩, _⟩
  exact localRankOneTypeB_false_of_oddQuadraticPresentation
    hpresentation d n e hn hsc has hnumbering.1 hrank

/-- The explicit component, centre and type-B prerequisites reduce the local
enumeration to the G2 and inner-or-no-fixed-leaf D4 patterns. -/
theorem localRankOneTitsIndex_or_G2_or_D4_of_oddQuadraticPresentation
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (hpresentation : TypeBOddQuadraticPresentationStatement.{u})
    (d : TitsIndexData G) (htype : d.HasIrreducibleCartanType)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) :
    ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasExceptionalResidualRankOneIndex := by
  rcases localRankOneTitsIndex_or_residual_of_componentFactor
      hfactor hclass hmove d htype hsc has hrank with hindex | hremaining
  · exact Or.inl hindex
  · rcases hremaining with hB | hG2 | hD4
    · exact (d.not_hasRankOneHigherBIndex_of_oddQuadraticPresentation
        hpresentation hsc has hrank hB).elim
    · exact Or.inr (Or.inl hG2)
    · exact Or.inr (Or.inr hD4)

/-- The exact published enumeration follows from the five explicit structural
prerequisites and exclusions of the concrete G2 and D4 residual patterns. -/
theorem localRankOneTitsIndex_of_oddQuadraticPresentation_and_remaining_inputs
    (hcartan : AbsolutelyAlmostSimpleCartanClassificationStatement.{u})
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (hpresentation : TypeBOddQuadraticPresentationStatement.{u})
    (hG2 :
      ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
        [IsNonarchimedeanLocalField k]
        (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
        [LocallyOfFiniteType H.X.hom] (e : TitsIndexData H),
        IsSimplyConnected H → IsAbsolutelyAlmostSimple H → splitRank H = 1 →
          ¬ e.HasRankOneG2Index)
    (hD4 :
      ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
        [IsNonarchimedeanLocalField k]
        (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
        [LocallyOfFiniteType H.X.hom] (e : TitsIndexData H),
        IsSimplyConnected H → IsAbsolutelyAlmostSimple H → splitRank H = 1 →
          ¬ e.HasRankOneD4InnerOrNoFixedLeafIndex) :
    LocalRankOneTitsIndexStatement.{u} := by
  intro k _ _ _ _ H _ _ e hsc has hrank
  rcases localRankOneTitsIndex_or_G2_or_D4_of_oddQuadraticPresentation
      hfactor hclass hmove hpresentation e (hcartan k H e has) hsc has hrank with
      hindex | hremaining
  · exact hindex
  · rcases hremaining with hG | hD
    · exact (hG2 k H e hsc has hrank hG).elim
    · exact (hD4 k H e hsc has hrank hD).elim

end Langlands.GroupScheme
