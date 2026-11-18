import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationStatement
import Langlands.GroupScheme.SimplyConnected.LocalRankOneResidualIndices
import Langlands.GroupScheme.SimplyConnected.RankOneInnerAIndex
import Langlands.GroupScheme.SimplyConnected.RankOneOuterAIndex
import Langlands.GroupScheme.SimplyConnected.LocalRankOneCIndex
import Langlands.GroupScheme.SimplyConnected.LocalRankOneBMarking
import Langlands.GroupScheme.SimplyConnected.TypeG2RankOneMarking
import Langlands.GroupScheme.SimplyConnected.LocalRankOneD4CentralMarking
import Langlands.GroupScheme.SimplyConnected.LocalRankOneDComponentBound
import Langlands.GroupScheme.SimplyConnected.LocalRankOneE6Marking
import Langlands.GroupScheme.SimplyConnected.LocalRankOneE7Marking
import Langlands.GroupScheme.SimplyConnected.LocalRankOneF4Exclusion
import Langlands.GroupScheme.SimplyConnected.LocalRankOneE8Exclusion
import Langlands.GroupScheme.SimplyConnected.LocalKernelCenterObstruction
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAProof

/-! # Reducing the local rank-one enumeration to three actual index patterns -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Exact component and Cartan information, together with exclusions for
both branch-marked type-E patterns, leaves only the three residual patterns
or the five desired indices. -/
theorem localRankOneTitsIndex_or_residual_of_typeE_exclusions
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (htype : d.HasIrreducibleCartanType)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1)
    (hE6 : ∀ (e : d.Vertex ≃ Fin 6),
      d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e → d.StarIsTrivial → False)
    (hE7 : ∀ (e : d.Vertex ≃ Fin 7),
      d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e → d.StarIsTrivial → False) :
    ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasResidualRankOneIndex := by
  classical
  rcases htype with hA | hB | hC | hD | hE₆ | hE₇ | hE8 | hF | hG
  · obtain ⟨n, hn, e, hA⟩ := hA
    by_cases hstar : d.StarIsTrivial
    · exact Or.inl (Or.inl
        (hasRankOneInnerAIndex_of_hasInnerTypeA d n hsc has
          ⟨by omega, ⟨e, hA⟩, hstar⟩ hrank))
    · exact Or.inl (Or.inr (Or.inl ⟨n,
        d.hasRankOneOuterAIndex_of_outer_type_A hsc has e hA hstar hrank⟩))
  · obtain ⟨n, hn, e, hB⟩ := hB
    by_cases hn2 : n = 2
    · subst n
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨2,
        (localRankOneTypeB_two_index d e hsc has hB hrank).2⟩)))
    · obtain ⟨⟨j, hj, hmark⟩, hstar⟩ :=
        localRankOneTypeB_marking_of_components hcomponents d hn e hB hrank
      exact Or.inr (Or.inl ⟨n, by omega, ⟨e, j, hj, hmark⟩, hstar⟩)
  · obtain ⟨n, hn, e, hC⟩ := hC
    exact Or.inl (Or.inr (Or.inr (Or.inl
      ⟨n, localRankOneTypeC_index d e hn hsc has hC hrank⟩)))
  · obtain ⟨n, hn, e, hD⟩ := hD
    by_cases hn4 : n = 4
    · subst n
      have hmark := d.localRankOneD4_central_marking e hsc has hD hrank
      by_cases hstar : d.StarIsTrivial
      · exact Or.inr (Or.inr (Or.inr ⟨e, hmark, Or.inl hstar⟩))
      · by_cases hfixed : ∃ a : d.Vertex, e a ≠ 1 ∧
          ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a
        · obtain ⟨a, ha, hfix⟩ := hfixed
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
            (d.hasRankOneOuterD4Index_of_fixed_leaf
              e hsc has hD a ha hfix hrank hstar)))))
        · exact Or.inr (Or.inr (Or.inr ⟨e, hmark, Or.inr hfixed⟩))
    · have hD5 := (localRankOneTypeD_innerD5_of_five_le_of_components
        hcomponents d e (by omega) hsc has hD hrank).2
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hD5))))
  · obtain ⟨e, hE⟩ := hE₆
    obtain ⟨hmark, hstar⟩ :=
      localRankOneTypeE6_marking_of_components hcomponents d e hE hsc hrank
    exact (hE6 e hmark hstar).elim
  · obtain ⟨e, hE⟩ := hE₇
    obtain ⟨hmark, hstar⟩ :=
      localRankOneTypeE7_marking_of_components hcomponents d e hE hrank
    exact (hE7 e hmark hstar).elim
  · obtain ⟨e, hE⟩ := hE8
    exact (localRankOneTypeE8_false_of_components hcomponents d e hE hrank).elim
  · obtain ⟨e, hF⟩ := hF
    exact (localRankOneTypeF4_false_of_components hcomponents d e hF hrank).elim
  · obtain ⟨e, hG⟩ := hG
    obtain ⟨hmark, hstar⟩ := d.G2_rankOne_marking e hG hrank
    exact Or.inr (Or.inr (Or.inl ⟨⟨e, hmark⟩, hstar⟩))

/-- The centre prerequisites supply both branch-marked type-E exclusions. -/
theorem localRankOneTitsIndex_or_residual_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (d : TitsIndexData G) (htype : d.HasIrreducibleCartanType)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) :
    ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasResidualRankOneIndex :=
  localRankOneTitsIndex_or_residual_of_typeE_exclusions hcomponents d htype hsc has hrank
    (fun e h hstar => d.not_E6_branch_mark_of_centerMovement hclass hmove hsc has hrank hstar e h)
    (fun e h hstar => d.not_E7_branch_mark_of_centerMovement hclass hmove hsc has hrank hstar e h)

/-- The component premise can be reduced to actual factor realization:
the unconditional local anisotropic type-A theorem supplies its other input. -/
theorem localRankOneTitsIndex_or_residual_of_componentFactor
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (d : TitsIndexData G) (htype : d.HasIrreducibleCartanType)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hrank : splitRank G = 1) :
    ((∃ degree : ℕ, d.HasRankOneInnerAIndex degree) ∨
      (∃ n : ℕ, d.HasRankOneOuterAIndex n) ∨
      (∃ n : ℕ, d.HasRankOneCIndex n) ∨
      d.HasRankOneOuterD4Index ∨ d.HasRankOneInnerD5Index) ∨
      d.HasResidualRankOneIndex :=
  localRankOneTitsIndex_or_residual_of_components
    (localAnisotropicCartanComponents_of_componentFactor hfactor localAnisotropicTypeA)
    hclass hmove d htype hsc has hrank

/-- Explicit remaining structural inputs and exclusion of the concrete
residual patterns suffice for the exact published enumeration. -/
theorem localRankOneTitsIndex_of_remaining_inputs
    (hcartan : AbsolutelyAlmostSimpleCartanClassificationStatement.{u})
    (hfactor : SemisimpleTitsComponentFactorStatement.{u})
    (hclass : NormOneCenterAutomorphismOppositeStatement.{u})
    (hmove : RankOneTypeEKernelCenterMovementStatement.{u})
    (hresidual :
      ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
        [IsNonarchimedeanLocalField k]
        (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
        [LocallyOfFiniteType H.X.hom] (e : TitsIndexData H),
        IsSimplyConnected H → IsAbsolutelyAlmostSimple H → splitRank H = 1 →
          ¬ e.HasResidualRankOneIndex) :
    LocalRankOneTitsIndexStatement.{u} := by
  intro k _ _ _ _ H _ _ e hsc has hrank
  rcases localRankOneTitsIndex_or_residual_of_componentFactor
      hfactor hclass hmove e (hcartan k H e has) hsc has hrank with hindex | hremaining
  · exact hindex
  · exact (hresidual k H e hsc has hrank hremaining).elim

end Langlands.GroupScheme
