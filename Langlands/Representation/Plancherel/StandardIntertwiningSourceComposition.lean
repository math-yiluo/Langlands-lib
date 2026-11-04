import Langlands.Representation.Plancherel.StandardIntertwiningCountableComposition
import Langlands.Representation.Plancherel.StandardIntertwiningSourceFactors

/-! # Standard-integral composition at the common ambient source scale -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration Haar

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- The first actual complement uses the inverse image of the same original
ambient compact open as the nested first complement. -/
def sourceFirstCompactOpen (Q : OpenSubgroup G) (hV : IsClosed (V : Set G)) :
    OpenSubgroup (V.subgroupOf U₁) :=
  compactOpenPreimage Q
    (V.subtype.comp D.firstComplementEquiv.toMonoidHom)
    (hV.isClosedEmbedding_subtypeVal.comp D.firstComplementEquiv.isClosedEmbedding)

/-- The canonical change of first-complement copies preserves the original
ambient compact open literally. -/
theorem firstCompactComplement_source (Q : OpenSubgroup G)
    (hV : IsClosed (V : Set G)) :
    D.firstCompactComplement (D.sourceNestedComplementCompactOpen Q hV) =
      D.sourceFirstCompactOpen Q hV := by
  ext v
  rfl

section EndpointRightInvariance

variable [IsTopologicalGroup G] [LocallyCompactSpace G]
  (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))
  (hU₀ : IsClosed (U₀ : Set G)) (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [hRightH : IsMulRightInvariant (D.sourceNestedKernelHaar Q hQ hU₀ hU₂)]

include hRightH in
/-- Exact transport of the nested source kernel carries its supplied right
invariance to the original endpoint intersection. -/
theorem sourceEndpointRightInvariant :
    IsMulRightInvariant (sourceIntersectionHaar Q hQ U₀ U₂ hU₀ hU₂) := by
  rw [← D.intersectionKernelMeasure_source Q hQ hU₀ hU₂]
  infer_instance

end EndpointRightInvariance

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
  [IsMulRightInvariant (sourceIntersectionHaar Q hQ U₀ U₁ hU₀ hU₁)]
  [IsMulRightInvariant (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)]
  [hRightH : IsMulRightInvariant (D.sourceNestedKernelHaar Q hQ hU₀ hU₂)]
  [IsMulRightInvariant (D.sourceNestedComplementHaar Q hQ hV)]
  [IsMulRightInvariant (D.sourceSecondComplementHaar Q hQ hW)]

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
  (hνH : IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
    (D.sourceNestedKernelHaar Q hQ hU₀ hU₂) νH)
  (hν₁₀ : IsCompatible (U₀.subgroupOf U₁)
    (subgroupCompactOpenHaar Q hQ U₁ hU₁)
    (sourceIntersectionHaar Q hQ U₀ U₁ hU₀ hU₁) ν₁₀)
  (hν₂₁ : IsCompatible (U₁.subgroupOf U₂)
    (subgroupCompactOpenHaar Q hQ U₂ hU₂)
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂) ν₂₁)
  (hν₂₀ : letI := D.sourceEndpointRightInvariant Q hQ hU₀ hU₂
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

include hU₂ hνH hν₁₀ hν₂₁ hν₂₀ hlocal₀ hlocal₁ hlocal₂ in
/-- Actual standard-integral composition at the common source Haar scale.
Compactness and all four unit-mass conditions are derived from `Q`; the same
four compatible quotient measures and both actual integral witnesses are kept. -/
theorem comp_hasIntegral_at_sourceScale
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
  let μU₁ := subgroupCompactOpenHaar Q hQ U₁ hU₁
  let μU₂ := subgroupCompactOpenHaar Q hQ U₂ hU₂
  let μI₁₀ := sourceIntersectionHaar Q hQ U₀ U₁ hU₀ hU₁
  let μI₂₁ := sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂
  let μH := D.sourceNestedKernelHaar Q hQ hU₀ hU₂
  let μK := D.sourceNestedComplementHaar Q hQ hV
  let μL := D.sourceSecondComplementHaar Q hQ hW
  let R := sourceTargetCompactOpen Q hU₁
  let S := sourceMiddleCompactOpen Q hU₁ hU₂
  let B := D.sourceNestedComplementCompactOpen Q hV
  let T := sourceTargetCompactOpen Q hU₂
  let C := D.sourceSecondComplementCompactOpen Q hW
  have hR : IsCompact (R : Set U₁) :=
    compactOpenPreimage_isCompact Q hQ _ _
  have hS : IsCompact (S : Set (U₁.subgroupOf U₂)) :=
    compactOpenPreimage_isCompact Q hQ _ _
  have hB : IsCompact
      (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) :=
    compactOpenPreimage_isCompact Q hQ _ _
  have hT : IsCompact (T : Set U₂) :=
    compactOpenPreimage_isCompact Q hQ _ _
  have hC : IsCompact (C : Set (W.subgroupOf U₂)) :=
    compactOpenPreimage_isCompact Q hQ _ _
  have hRmass : μU₁ (R : Set U₁) = 1 :=
    subgroupCompactOpenHaar_mass Q hQ U₁ hU₁
  have hI₁₀mass : μI₁₀ {h : U₀.subgroupOf U₁ | h.val ∈ R} = 1 :=
    sourceIntersectionHaar_mass Q hQ U₀ U₁ hU₀ hU₁
  have hSmass : μI₂₁ (S : Set (U₁.subgroupOf U₂)) = 1 :=
    sourceIntersectionHaar_mass Q hQ U₁ U₂ hU₁ hU₂
  have hHmass : μH
      {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) | h.val ∈ S} = 1 :=
    D.sourceNestedKernelHaar_mass Q hQ hU₀ hU₂
  have hlocal₀' : D.firstSubgroupProduct ''
      ({h : U₀.subgroupOf U₁ | h.val ∈ R} ×ˢ
        (D.firstCompactComplement B : Set (V.subgroupOf U₁))) = (R : Set U₁) := by
    dsimp only [B, R]
    rw [D.firstCompactComplement_source Q hV]
    exact hlocal₀
  have hν₂₀' : IsCompatible (U₀.subgroupOf U₂) μU₂
      (D.intersectionKernelMeasure μH) ν₂₀ := by
    dsimp only [μU₂, μH]
    simpa only [D.intersectionKernelMeasure_source Q hQ hU₀ hU₂] using hν₂₀
  have ha' : OrderedScalarIntegrable h₀ hU₀ A
      (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
      (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) f := by
    dsimp only [μI₂₁, μH, μK, μU₂, μL, S, B, T, C]
    rw [D.intersectionNormalizedFactor_source Q hQ hV hU₀ hU₁ hU₂,
      D.secondNormalizedFactor_source Q hQ hW hU₁ hU₂]
    exact ha
  exact D.comp_hasIntegral_of_secondCountable
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ μU₁ μI₁₀ ν₁₀ ν₂₀
    hν₁₀ hν₂₀' R hR hlocal₀' hRmass hI₁₀mass hSmass hHmass h₀ h₁ A hf hF ha'

end Integral

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
