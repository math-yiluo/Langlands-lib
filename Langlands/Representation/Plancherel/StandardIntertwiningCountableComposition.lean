import Langlands.Representation.Plancherel.StandardIntertwiningFactorRegularity
import Mathlib.Topology.Metrizable.Urysohn

/-! # Countable topology for standard-intertwining composition -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

set_option linter.defProp false in
/-- Local compactness of the first complement follows from its supplied chart
and closedness of its target subgroup. -/
@[instance_reducible]
def firstComplementLocallyCompactSpace [LocallyCompactSpace G]
    (hU₁ : IsClosed (U₁ : Set G)) : LocallyCompactSpace V := by
  let : LocallyCompactSpace U₁ := hU₁.locallyCompactSpace
  let : LocallyCompactSpace ((U₀.subgroupOf U₁) × V) :=
    D.first.isClosedEmbedding.locallyCompactSpace
  exact (isOpenQuotientMap_snd (X := U₀.subgroupOf U₁) (Y := V)).locallyCompactSpace

set_option linter.defProp false in
/-- Local compactness of the second complement follows from its supplied chart
and closedness of its target subgroup. -/
@[instance_reducible]
def secondComplementLocallyCompactSpace [LocallyCompactSpace G]
    (hU₂ : IsClosed (U₂ : Set G)) : LocallyCompactSpace W := by
  let : LocallyCompactSpace U₂ := hU₂.locallyCompactSpace
  let : LocallyCompactSpace ((U₁.subgroupOf U₂) × W) :=
    D.second.isClosedEmbedding.locallyCompactSpace
  exact (isOpenQuotientMap_snd (X := U₁.subgroupOf U₂) (Y := W)).locallyCompactSpace


section IntegralFromSecondCountability

open Induction

local instance subgroupSecondCountable {H : Type*} [Group H]
    [TopologicalSpace H] [SecondCountableTopology H] (K : Subgroup H) :
    SecondCountableTopology K :=
  TopologicalSpace.Subtype.secondCountableTopology (K : Set H)

variable [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
  [scG : SecondCountableTopology G]
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μL : Measure (W.subgroupOf U₂))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (T : OpenSubgroup U₂) (C : OpenSubgroup (W.subgroupOf U₂))
  [IsHaarMeasure μU₂]
  [IsHaarMeasure μI₂₁] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μH] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [IsMulRightInvariant μK]
  [IsHaarMeasure μL] [IsMulRightInvariant μL]
  [MeasurableSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  (νH : Measure (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
  (ν₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (hνH : IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    μI₂₁ μH νH)
  (hν₂₁ : IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
  (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
  (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
  (hlocal₁ : D.intersectionSubgroupProduct ''
    ({h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        (h : U₁.subgroupOf U₂) ∈ S} ×ˢ
      (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) =
    (S : Set (U₁.subgroupOf U₂)))
  (hT : IsCompact (T : Set U₂)) (hC : IsCompact (C : Set (W.subgroupOf U₂)))
  (hlocal₂ : D.secondSubgroupProduct ''
    ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T} ×ˢ
      (C : Set (W.subgroupOf U₂))) = (T : Set U₂))


variable
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [IsHaarMeasure μU₁]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  [IsHaarMeasure μI₁₀] [IsMulRightInvariant μI₁₀]
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hν₂₀ : IsCompatible (U₀.subgroupOf U₂) μU₂
    (D.intersectionKernelMeasure μH) ν₂₀)
  (R : OpenSubgroup U₁) (hR : IsCompact (R : Set U₁))
  (hlocal₀ : D.firstSubgroupProduct ''
    ({h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} ×ˢ
      (D.firstCompactComplement B : Set (V.subgroupOf U₁))) = (R : Set U₁))
  (hRmass : μU₁ (R : Set U₁) = 1)
  (hI₁₀mass : μI₁₀ {h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} = 1)
  (hSmass : μI₂₁ (S : Set (U₁.subgroupOf U₂)) = 1)
  (hHmass : μH {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
    (h : U₁.subgroupOf U₂) ∈ S} = 1)


variable
  {P₀ P₁ M : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

include scG hU₂ hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ hν₁₀ hν₂₀
  hR hlocal₀ hRmass hI₁₀mass hSmass hHmass in
/-- Actual standard-integral composition with all measure regularity,
S-finiteness and product Borel structures derived from ambient second
countability, local compactness, closedness and the supplied charts. -/
theorem comp_hasIntegral_of_secondCountable
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A
      (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
      (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) f) :
    HasIntegral h₀ hU₀ U₂ A ν₂₀ f J := by
  let : LocallyCompactSpace U₁ := hU₁.locallyCompactSpace
  let : LocallyCompactSpace U₂ := hU₂.locallyCompactSpace
  have hI₂₁ : IsClosed (U₁.subgroupOf U₂ : Set U₂) :=
    hU₁.preimage (continuous_subtype_val : Continuous (Subtype.val : U₂ → G))
  let : LocallyCompactSpace (U₁.subgroupOf U₂) := hI₂₁.locallyCompactSpace
  have hI₁₀ : IsClosed (U₀.subgroupOf U₁ : Set U₁) :=
    hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : U₁ → G))
  let : LocallyCompactSpace (U₀.subgroupOf U₁) := hI₁₀.locallyCompactSpace
  have hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)) :=
    hU₀.preimage
      ((continuous_subtype_val : Continuous (Subtype.val : U₂ → G)).comp
        (continuous_subtype_val :
          Continuous (Subtype.val : (U₁.subgroupOf U₂) → U₂)))
  let : LocallyCompactSpace
      ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) := hH.locallyCompactSpace
  let : LocallyCompactSpace V := D.firstComplementLocallyCompactSpace hU₁
  let : LocallyCompactSpace W := D.secondComplementLocallyCompactSpace hU₂
  let : LocallyCompactSpace
      ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :=
    D.intersectionComplementEquiv.isClosedEmbedding.locallyCompactSpace
  let : LocallyCompactSpace (W.subgroupOf U₂) :=
    D.secondComplementEquiv.isClosedEmbedding.locallyCompactSpace
  exact D.comp_hasIntegral_of_seedRegularity
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ μU₁ μI₁₀ ν₁₀ ν₂₀
    hν₁₀ hν₂₀ R hR hlocal₀ hRmass hI₁₀mass hSmass hHmass h₀ h₁ A hf hF ha

end IntegralFromSecondCountability

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
