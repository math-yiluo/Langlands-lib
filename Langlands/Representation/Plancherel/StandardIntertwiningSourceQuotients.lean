import Langlands.Representation.Plancherel.StandardIntertwiningCoveredSourceComposition

/-! # Actual quotient measures at the common ambient source scale -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration Haar

universe uG uV

section QuotientMeasures

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))

/-- A genuine cover of an original closed subgroup makes its intrinsic
source Haar measure right invariant. -/
theorem sourceSubgroupHaar_rightInvariant_of_cover
    (B : Subgroup G) (hB : IsClosed (B : Set G))
    [MeasurableSpace B] [BorelSpace B]
    (hcover : ∀ b : B, ∃ C : OpenSubgroup B, IsCompact (C : Set B) ∧ b ∈ C) :
    IsMulRightInvariant (subgroupCompactOpenHaar Q hQ B hB) := by
  unfold subgroupCompactOpenHaar
  exact compactOpenHaarAlong_isMulRightInvariant_of_cover Q hQ
    B.subtype hB.isClosedEmbedding_subtypeVal hcover

section OrdinaryQuotient

variable (A B : Subgroup G)
  (hA : IsClosed (A : Set G)) (hB : IsClosed (B : Set G))
  [MeasurableSpace B] [BorelSpace B]
  [MeasurableSpace (A.subgroupOf B)] [BorelSpace (A.subgroupOf B)]
  [MeasurableSpace (QuotientSpace (U := A) B)]
  [BorelSpace (QuotientSpace (U := A) B)]
  (hcoverA : ∀ a : A, ∃ C : OpenSubgroup A, IsCompact (C : Set A) ∧ a ∈ C)
  (hcoverB : ∀ b : B, ∃ C : OpenSubgroup B, IsCompact (C : Set B) ∧ b ∈ C)

/-- Choose the actual intersection quotient only from proved existence for
the two exact source Haar measures, before receiving integral witnesses. -/
def sourceQuotientMeasure : Measure (QuotientSpace (U := A) B) := by
  let := hB.locallyCompactSpace
  let := sourceSubgroupHaar_rightInvariant_of_cover Q hQ B hB hcoverB
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ A B hA hB hcoverA
  exact Classical.choose (compatibleMeasureExists (A.subgroupOf B)
    (hA.preimage continuous_subtype_val)
    (subgroupCompactOpenHaar Q hQ B hB)
    (sourceIntersectionHaar Q hQ A B hA hB))

/-- The chosen quotient satisfies the full complex Weil compatibility
property at exactly the original ambient source scale. -/
theorem sourceQuotientMeasure_isCompatible :
    letI := sourceIntersectionHaar_rightInvariant_of_cover Q hQ A B hA hB hcoverA
    IsCompatible (A.subgroupOf B)
      (subgroupCompactOpenHaar Q hQ B hB)
      (sourceIntersectionHaar Q hQ A B hA hB)
      (sourceQuotientMeasure Q hQ A B hA hB hcoverA hcoverB) := by
  let := hB.locallyCompactSpace
  let := sourceSubgroupHaar_rightInvariant_of_cover Q hQ B hB hcoverB
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ A B hA hB hcoverA
  exact Classical.choose_spec (compatibleMeasureExists (A.subgroupOf B)
    (hA.preimage continuous_subtype_val)
    (subgroupCompactOpenHaar Q hQ B hB)
    (sourceIntersectionHaar Q hQ A B hA hB))

instance sourceQuotientMeasure_regular :
    (sourceQuotientMeasure Q hQ A B hA hB hcoverA hcoverB).Regular := by
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ A B hA hB hcoverA
  exact (sourceQuotientMeasure_isCompatible Q hQ A B hA hB hcoverA hcoverB).regular

theorem sourceQuotientMeasure_ne_zero :
    sourceQuotientMeasure Q hQ A B hA hB hcoverA hcoverB ≠ 0 := by
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ A B hA hB hcoverA
  exact (sourceQuotientMeasure_isCompatible Q hQ A B hA hB hcoverA hcoverB).nonzero

end OrdinaryQuotient

variable {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

section NestedQuotient

variable (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace (QuotientIntegration.LeftQuotient
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  (hcover₀ : ∀ u : U₀, ∃ C : OpenSubgroup U₀, IsCompact (C : Set U₀) ∧ u ∈ C)
  (hcover₁ : ∀ u : U₁, ∃ C : OpenSubgroup U₁, IsCompact (C : Set U₁) ∧ u ∈ C)

/-- The nested quotient is constructed from its exact intrinsic kernel and
ambient intersection measures, without identifying or rescaling quotients. -/
def sourceNestedQuotientMeasure :
    Measure (QuotientIntegration.LeftQuotient
      ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) := by
  let : LocallyCompactSpace (U₁.subgroupOf U₂) :=
    (intersectionAmbientHom_isClosedEmbedding U₁ U₂ hU₁ hU₂).locallyCompactSpace
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ U₁ U₂ hU₁ hU₂ hcover₁
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
  exact Classical.choose (compatibleMeasureExists
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    ((hU₀.preimage continuous_subtype_val).preimage continuous_subtype_val)
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
    (D.sourceNestedKernelHaar Q hQ hU₀ hU₂))

/-- The selected nested quotient is compatible with precisely the measures
used in actual source-scale composition. -/
theorem sourceNestedQuotientMeasure_isCompatible :
    letI := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
    IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
      (D.sourceNestedKernelHaar Q hQ hU₀ hU₂)
      (D.sourceNestedQuotientMeasure Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁) := by
  let : LocallyCompactSpace (U₁.subgroupOf U₂) :=
    (intersectionAmbientHom_isClosedEmbedding U₁ U₂ hU₁ hU₂).locallyCompactSpace
  let := sourceIntersectionHaar_rightInvariant_of_cover Q hQ U₁ U₂ hU₁ hU₂ hcover₁
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
  exact Classical.choose_spec (compatibleMeasureExists
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    ((hU₀.preimage continuous_subtype_val).preimage continuous_subtype_val)
    (sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂)
    (D.sourceNestedKernelHaar Q hQ hU₀ hU₂))

instance sourceNestedQuotientMeasure_regular :
    (D.sourceNestedQuotientMeasure Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁).Regular := by
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
  exact (D.sourceNestedQuotientMeasure_isCompatible Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁).regular

theorem sourceNestedQuotientMeasure_ne_zero :
    D.sourceNestedQuotientMeasure Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁ ≠ 0 := by
  let := D.sourceNestedKernelHaar_rightInvariant_of_cover Q hQ hU₀ hU₂ hcover₀
  exact (D.sourceNestedQuotientMeasure_isCompatible Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁).nonzero

end NestedQuotient

end QuotientMeasures

section Integral

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)
  [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
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
  (hcover₀ : ∀ u : U₀, ∃ C : OpenSubgroup U₀, IsCompact (C : Set U₀) ∧ u ∈ C)
  (hcover₁ : ∀ u : U₁, ∃ C : OpenSubgroup U₁, IsCompact (C : Set U₁) ∧ u ∈ C)
  (hcover₂ : ∀ u : U₂, ∃ C : OpenSubgroup U₂, IsCompact (C : Set U₂) ∧ u ∈ C)
  (hcoverV : ∀ v : V, ∃ C : OpenSubgroup V, IsCompact (C : Set V) ∧ v ∈ C)
  (hcoverW : ∀ w : W, ∃ C : OpenSubgroup W, IsCompact (C : Set W) ∧ w ∈ C)
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

include hcoverV hcoverW hlocal₀ hlocal₁ hlocal₂ in
/-- Actual composition for quotient measures constructed at the source scale
before the two integral witnesses are supplied. Compatibility is proved. -/
theorem comp_hasIntegral_at_sourceQuotients
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A
      (sourceQuotientMeasure Q hQ U₀ U₁ hU₀ hU₁ hcover₀ hcover₁) f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A
      (sourceQuotientMeasure Q hQ U₁ U₂ hU₁ hU₂ hcover₁ hcover₂) F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A
      (subgroupCompactOpenHaar Q hQ V hV)
      (subgroupCompactOpenHaar Q hQ W hW) f) :
    HasIntegral h₀ hU₀ U₂ A
      (sourceQuotientMeasure Q hQ U₀ U₂ hU₀ hU₂ hcover₀ hcover₂) f J := by
  exact D.comp_hasIntegral_at_sourceScale_of_covers
    Q hQ hU₀ hU₁ hU₂ hV hW hcover₀ hcover₁ hcoverV hcoverW
    (D.sourceNestedQuotientMeasure Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁)
    (sourceQuotientMeasure Q hQ U₀ U₁ hU₀ hU₁ hcover₀ hcover₁)
    (sourceQuotientMeasure Q hQ U₁ U₂ hU₁ hU₂ hcover₁ hcover₂)
    (sourceQuotientMeasure Q hQ U₀ U₂ hU₀ hU₂ hcover₀ hcover₂)
    (D.sourceNestedQuotientMeasure_isCompatible Q hQ hU₀ hU₁ hU₂ hcover₀ hcover₁)
    (sourceQuotientMeasure_isCompatible Q hQ U₀ U₁ hU₀ hU₁ hcover₀ hcover₁)
    (sourceQuotientMeasure_isCompatible Q hQ U₁ U₂ hU₁ hU₂ hcover₁ hcover₂)
    (sourceQuotientMeasure_isCompatible Q hQ U₀ U₂ hU₀ hU₂ hcover₀ hcover₂)
    hlocal₀ hlocal₁ hlocal₂ h₀ h₁ A hf hF ha

end Integral

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
