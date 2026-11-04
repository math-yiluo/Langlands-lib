import Langlands.Representation.Plancherel.StandardIntertwiningLocallyNormalizedComposition

/-! # Auxiliary-choice independence of normalized intertwining factors -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

section Intersection

variable [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  (μI₂₁ : Measure (U₁.subgroupOf U₂)) (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK μK' : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  [IsHaarMeasure μK'] [μK'.Regular] [IsMulRightInvariant μK']
  [MeasurableSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  {νH : Measure (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))}
  (S S' : OpenSubgroup (U₁.subgroupOf U₂))
  (B B' : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))

omit [BorelSpace V] in
/-- The actual first-complement measure is unchanged by auxiliary seed Haar
and compact-open choices satisfying their respective local product identities. -/
theorem intersectionNormalizedFactor_eq_of_localProducts
    (hνH : IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) μI₂₁ μH νH)
    (hH : IsClosed (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) : Set (U₁.subgroupOf U₂)))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hlocal : D.intersectionSubgroupProduct ''
      ({h : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) | (h : U₁.subgroupOf U₂) ∈ S} ×ˢ
        (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) = (S : Set (U₁.subgroupOf U₂)))
    (hS' : IsCompact (S' : Set (U₁.subgroupOf U₂)))
    (hB' : IsCompact (B' : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hlocal' : D.intersectionSubgroupProduct ''
      ({h : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) | (h : U₁.subgroupOf U₂) ∈ S'} ×ˢ
        (B' : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) = (S' : Set (U₁.subgroupOf U₂))) :
    D.intersectionNormalizedFactor μI₂₁ μH μK S B =
      D.intersectionNormalizedFactor μI₂₁ μH μK' S' B' := by
  unfold intersectionNormalizedFactor
  exact congrArg (Measure.map D.intersectionComplementEquiv)
    (hνH.compactOpenFactorMeasure_eq_of_localProducts ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      μI₂₁ μH μK S B D.intersectionSubgroupProduct
      D.intersectionSubgroupProduct_eq hH hS hB hlocal μK' S' B' hS' hB' hlocal')

end Intersection

section Second

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace U₂]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μL μL' : Measure (W.subgroupOf U₂))
  [IsHaarMeasure μU₂] [μU₂.Regular]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μL] [μL.Regular] [IsMulRightInvariant μL]
  [IsHaarMeasure μL'] [μL'.Regular] [IsMulRightInvariant μL']
  [MeasurableSpace (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))]
  [BorelSpace (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))]
  {ν₂₁ : Measure (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))}
  (T T' : OpenSubgroup U₂) (C C' : OpenSubgroup (W.subgroupOf U₂))

omit [BorelSpace W] in
/-- The actual second-complement measure is unchanged by auxiliary seed Haar
and compact-open choices, with ambient and intersection measures fixed. -/
theorem secondNormalizedFactor_eq_of_localProducts
    (hν₂₁ : IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
    (hI : IsClosed (U₁.subgroupOf U₂ : Set U₂))
    (hT : IsCompact (T : Set U₂)) (hC : IsCompact (C : Set (W.subgroupOf U₂)))
    (hlocal : D.secondSubgroupProduct ''
      ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T} ×ˢ
        (C : Set (W.subgroupOf U₂))) = (T : Set U₂))
    (hT' : IsCompact (T' : Set U₂)) (hC' : IsCompact (C' : Set (W.subgroupOf U₂)))
    (hlocal' : D.secondSubgroupProduct ''
      ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T'} ×ˢ
        (C' : Set (W.subgroupOf U₂))) = (T' : Set U₂)) :
    D.secondNormalizedFactor μU₂ μI₂₁ μL T C =
      D.secondNormalizedFactor μU₂ μI₂₁ μL' T' C' := by
  unfold secondNormalizedFactor
  exact congrArg (Measure.map D.secondComplementEquiv)
    (hν₂₁.compactOpenFactorMeasure_eq_of_localProducts
      (U₁.subgroupOf U₂) (W.subgroupOf U₂) μU₂ μI₂₁ μL T C
      D.secondSubgroupProduct D.secondSubgroupProduct_eq hI hT hC hlocal
      μL' T' C' hT' hC' hlocal')

end Second

section Product

variable [IsTopologicalGroup G]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μL : Measure (W.subgroupOf U₂))
  (S : OpenSubgroup (U₁.subgroupOf U₂)) (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (T : OpenSubgroup U₂) (C : OpenSubgroup (W.subgroupOf U₂))

/-- The ordered product measure on the original two complement carriers,
using the explicit local volume normalization of each factor. -/
def normalizedComplementProductMeasure : Measure (V × W) :=
  (D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)

variable [T2Space G] [LocallyCompactSpace U₂]
  [LocallyCompactSpace (U₁.subgroupOf U₂)]
  [IsHaarMeasure μU₂] [μU₂.Regular]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  [IsHaarMeasure μL] [μL.Regular] [IsMulRightInvariant μL]
  (μK' : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) (μL' : Measure (W.subgroupOf U₂))
  [IsHaarMeasure μK'] [μK'.Regular] [IsMulRightInvariant μK']
  [IsHaarMeasure μL'] [μL'.Regular] [IsMulRightInvariant μL']
  [MeasurableSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [MeasurableSpace (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))]
  [BorelSpace (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))]
  {νH : Measure (QuotientIntegration.LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))}
  {ν₂₁ : Measure (QuotientIntegration.LeftQuotient (U₁.subgroupOf U₂))}
  (S' : OpenSubgroup (U₁.subgroupOf U₂)) (B' : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (T' : OpenSubgroup U₂) (C' : OpenSubgroup (W.subgroupOf U₂))

omit [BorelSpace V] [BorelSpace W] in
/-- Both auxiliary choices can be varied independently without changing the
ordered measure used by scalar Fubini in standard-intertwining composition. -/
theorem normalizedComplementProductMeasure_eq_of_localProducts
    (hνH : IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) μI₂₁ μH νH)
    (hν₂₁ : IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
    (hH : IsClosed (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) : Set (U₁.subgroupOf U₂)))
    (hI : IsClosed (U₁.subgroupOf U₂ : Set U₂))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hlocal₁ : D.intersectionSubgroupProduct ''
      ({h : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) | (h : U₁.subgroupOf U₂) ∈ S} ×ˢ
        (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) = (S : Set (U₁.subgroupOf U₂)))
    (hT : IsCompact (T : Set U₂)) (hC : IsCompact (C : Set (W.subgroupOf U₂)))
    (hlocal₂ : D.secondSubgroupProduct ''
      ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T} ×ˢ
        (C : Set (W.subgroupOf U₂))) = (T : Set U₂))
    (hS' : IsCompact (S' : Set (U₁.subgroupOf U₂)))
    (hB' : IsCompact (B' : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hlocal₁' : D.intersectionSubgroupProduct ''
      ({h : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) | (h : U₁.subgroupOf U₂) ∈ S'} ×ˢ
        (B' : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) = (S' : Set (U₁.subgroupOf U₂)))
    (hT' : IsCompact (T' : Set U₂)) (hC' : IsCompact (C' : Set (W.subgroupOf U₂)))
    (hlocal₂' : D.secondSubgroupProduct ''
      ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T'} ×ˢ
        (C' : Set (W.subgroupOf U₂))) = (T' : Set U₂)) :
    D.normalizedComplementProductMeasure μU₂ μI₂₁ μH μK μL S B T C =
      D.normalizedComplementProductMeasure μU₂ μI₂₁ μH μK' μL' S' B' T' C' := by
  unfold normalizedComplementProductMeasure
  rw [D.intersectionNormalizedFactor_eq_of_localProducts μI₂₁ μH μK μK' S S' B B'
    hνH hH hS hB hlocal₁ hS' hB' hlocal₁',
    D.secondNormalizedFactor_eq_of_localProducts μU₂ μI₂₁ μL μL' T T' C C'
      hν₂₁ hI hT hC hlocal₂ hT' hC' hlocal₂']

end Product

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
