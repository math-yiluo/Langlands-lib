import Langlands.Representation.Plancherel.StandardIntertwiningSourceComposition

/-! # Source-scale composition from covers of the original groups -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration Haar

universe uG uH uL uV

private theorem compactOpenCover_preimage
    {H : Type uH} [Group H] [TopologicalSpace H]
    {L : Type uL} [Group L] [TopologicalSpace L]
    (ι : H →* L) (hι : Topology.IsClosedEmbedding (ι : H → L))
    (hcover : ∀ l : L, ∃ C : OpenSubgroup L, IsCompact (C : Set L) ∧ l ∈ C)
    (h : H) :
    ∃ C : OpenSubgroup H, IsCompact (C : Set H) ∧ h ∈ C := by
  obtain ⟨C, hC, hh⟩ := hcover (ι h)
  exact ⟨C.comap ι hι.continuous, hι.isCompact_preimage hC, hh⟩

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual intersection includes into its original source group by
forgetting the target-subgroup wrapper. -/
def intersectionSourceHom (A B : Subgroup G) : A.subgroupOf B →* A where
  toFun h := ⟨h.val.val, h.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Closed original subgroups make the actual intersection a closed
embedded subgroup of its original source carrier. -/
theorem intersectionSourceHom_isClosedEmbedding
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G)) :
    Topology.IsClosedEmbedding (intersectionSourceHom A B : A.subgroupOf B → A) := by
  apply Topology.IsClosedEmbedding.of_comp (g := (Subtype.val : A → G))
    Topology.IsEmbedding.subtypeVal
  exact intersectionAmbientHom_isClosedEmbedding A B hA hB

section RightInvariance

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))

/-- A cover of the original source group gives right invariance of its
actual intersection's intrinsic source Haar measure. -/
theorem sourceIntersectionHaar_rightInvariant_of_cover
    (A B : Subgroup G) (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
    [MeasurableSpace (A.subgroupOf B)] [BorelSpace (A.subgroupOf B)]
    (hcover : ∀ a : A, ∃ C : OpenSubgroup A, IsCompact (C : Set A) ∧ a ∈ C) :
    IsMulRightInvariant (sourceIntersectionHaar Q hQ A B hA hB) := by
  unfold sourceIntersectionHaar
  apply compactOpenHaarAlong_isMulRightInvariant_of_cover
  exact compactOpenCover_preimage (intersectionSourceHom A B)
    (intersectionSourceHom_isClosedEmbedding A B hA hB) hcover

variable {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- The original source cover also covers the actual nested endpoint
kernel and makes its intrinsic source Haar measure right invariant. -/
theorem sourceNestedKernelHaar_rightInvariant_of_cover
    (hU₀ : IsClosed (U₀ : Set G)) (hU₂ : IsClosed (U₂ : Set G))
    [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
    [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
    [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
    (hcover : ∀ u : U₀, ∃ C : OpenSubgroup U₀, IsCompact (C : Set U₀) ∧ u ∈ C) :
    IsMulRightInvariant (D.sourceNestedKernelHaar Q hQ hU₀ hU₂) := by
  unfold sourceNestedKernelHaar
  apply compactOpenHaarAlong_isMulRightInvariant_of_cover
  exact compactOpenCover_preimage
    ((intersectionSourceHom U₀ U₂).comp D.intersectionKernelEquiv.toMonoidHom)
    ((intersectionSourceHom_isClosedEmbedding U₀ U₂ hU₀ hU₂).comp
      D.intersectionKernelEquiv.isClosedEmbedding) hcover

/-- A cover of the original first complement suffices for right
invariance on its actual nested copy. -/
theorem sourceNestedComplementHaar_rightInvariant_of_cover
    (hV : IsClosed (V : Set G))
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
    [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
    (hcover : ∀ v : V, ∃ C : OpenSubgroup V, IsCompact (C : Set V) ∧ v ∈ C) :
    IsMulRightInvariant (D.sourceNestedComplementHaar Q hQ hV) := by
  unfold sourceNestedComplementHaar
  apply compactOpenHaarAlong_isMulRightInvariant_of_cover
  exact compactOpenCover_preimage D.intersectionComplementEquiv.toMonoidHom
    D.intersectionComplementEquiv.isClosedEmbedding hcover

/-- A cover of the original second complement suffices for right
invariance on its actual subgroup copy. -/
theorem sourceSecondComplementHaar_rightInvariant_of_cover
    (hW : IsClosed (W : Set G))
    [MeasurableSpace W] [BorelSpace W]
    [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
    (hcover : ∀ w : W, ∃ C : OpenSubgroup W, IsCompact (C : Set W) ∧ w ∈ C) :
    IsMulRightInvariant (D.sourceSecondComplementHaar Q hQ hW) := by
  unfold sourceSecondComplementHaar
  apply compactOpenHaarAlong_isMulRightInvariant_of_cover
  exact compactOpenCover_preimage D.secondComplementEquiv.toMonoidHom
    D.secondComplementEquiv.isClosedEmbedding hcover

end RightInvariance

variable {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

section Integral

open Induction

variable [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
  (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  (hV : IsClosed (V : Set G)) (hW : IsClosed (W : Set G))
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
  (hcover₀ : ∀ u : U₀, ∃ C : OpenSubgroup U₀, IsCompact (C : Set U₀) ∧ u ∈ C)
  (hcover₁ : ∀ u : U₁, ∃ C : OpenSubgroup U₁, IsCompact (C : Set U₁) ∧ u ∈ C)
  (hcoverV : ∀ v : V, ∃ C : OpenSubgroup V, IsCompact (C : Set V) ∧ v ∈ C)
  (hcoverW : ∀ w : W, ∃ C : OpenSubgroup W, IsCompact (C : Set W) ∧ w ∈ C)

variable
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  (νH : Measure (QuotientIntegration.LeftQuotient
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hνH : letI := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
    IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
    (D.sourceNestedKernelHaar Q hQ hU₀ hU₂) νH)
  (hν₁₀ : letI := sourceIntersectionHaar_rightInvariant_of_cover Q hQ U₀ U₁ hU₀ hU₁ hcover₀
    IsCompatible (U₀.subgroupOf U₁)
    (subgroupCompactOpenHaar Q hQ U₁ hU₁)
    (sourceIntersectionHaar Q hQ U₀ U₁ hU₀ hU₁) ν₁₀)
  (hν₂₁ : letI := sourceIntersectionHaar_rightInvariant_of_cover Q hQ U₁ U₂ hU₁ hU₂ hcover₁
    IsCompatible (U₁.subgroupOf U₂)
    (subgroupCompactOpenHaar Q hQ U₂ hU₂)
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂) ν₂₁)
  (hν₂₀ : letI := sourceIntersectionHaar_rightInvariant_of_cover Q hQ U₀ U₂ hU₀ hU₂ hcover₀
    IsCompatible (U₀.subgroupOf U₂)
      (subgroupCompactOpenHaar Q hQ U₂ hU₂)
      (sourceIntersectionHaar Q hQ U₀ U₂ hU₀ hU₂) ν₂₀)
  (hlocal₀ : D.firstSubgroupProduct ''
    ({h : U₀.subgroupOf U₁ | h.val ∈ sourceTargetCompactOpen Q hU₁} ×ˢ
      (D.sourceFirstCompactOpen Q hV : Set (V.subgroupOf U₁))) =
        (sourceTargetCompactOpen Q hU₁ : Set U₁))
  (hlocal₁ : D.intersectionSubgroupProduct ''
    ({h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        h.val ∈ sourceMiddleCompactOpen Q hU₁ hU₂} ×ˢ
      (D.sourceNestedComplementCompactOpen Q hV :
        Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) =
      (sourceMiddleCompactOpen Q hU₁ hU₂ : Set (U₁.subgroupOf U₂)))
  (hlocal₂ : D.secondSubgroupProduct ''
    ({h : U₁.subgroupOf U₂ | h.val ∈ sourceTargetCompactOpen Q hU₂} ×ˢ
      (D.sourceSecondComplementCompactOpen Q hW : Set (W.subgroupOf U₂))) =
      (sourceTargetCompactOpen Q hU₂ : Set U₂))
  {P₀ P₁ M : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

include hU₂ hcover₀ hcover₁ hcoverV hcoverW
  hνH hν₁₀ hν₂₁ hν₂₀ hlocal₀ hlocal₁ hlocal₂ in
/-- Actual source-scale composition with all five required right-invariance
facts derived from covers of the four original groups. The same quotient
measures, local geometries, intermediate section and integral witnesses remain. -/
theorem comp_hasIntegral_at_sourceScale_of_covers
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A
      (subgroupCompactOpenHaar Q hQ V hV)
      (subgroupCompactOpenHaar Q hQ W hW) f) :
    HasIntegral h₀ hU₀ U₂ A ν₂₀ f J := by
  let := sourceIntersectionHaar_rightInvariant_of_cover
    Q hQ U₀ U₁ hU₀ hU₁ hcover₀
  let := sourceIntersectionHaar_rightInvariant_of_cover
    Q hQ U₁ U₂ hU₁ hU₂ hcover₁
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
  let := D.sourceNestedComplementHaar_rightInvariant_of_cover Q hQ hV hcoverV
  let := D.sourceSecondComplementHaar_rightInvariant_of_cover Q hQ hW hcoverW
  exact D.comp_hasIntegral_at_sourceScale Q hQ hU₀ hU₁ hU₂ hV hW
    νH ν₁₀ ν₂₁ ν₂₀ hνH hν₁₀ hν₂₁ hν₂₀ hlocal₀ hlocal₁ hlocal₂ h₀ h₁ A hf hF ha

end Integral

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
