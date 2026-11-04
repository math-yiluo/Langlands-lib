import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Representation.Plancherel.StandardIntertwiningIntersectionNormalization

/-! # Standard-integral composition with locally normalized factor measures -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- The second complement inside the actual target subgroup has its original
group carrier and topology. -/
def secondComplementEquiv : W.subgroupOf U₂ ≃ₜ* W :=
  subgroupOfContinuousEquiv D.second_le

/-- The second chart on actual subgroups of its target, in the original order. -/
def secondSubgroupProduct : (U₁.subgroupOf U₂) × (W.subgroupOf U₂) ≃ₜ U₂ :=
  ((Homeomorph.refl (U₁.subgroupOf U₂)).prodCongr
    D.secondComplementEquiv.toHomeomorph).trans D.second

theorem secondSubgroupProduct_eq (p : (U₁.subgroupOf U₂) × (W.subgroupOf U₂)) :
    D.secondSubgroupProduct p = p.1.val * p.2.val := by
  apply Subtype.ext
  exact congrArg (fun z : U₂ => z.val) (D.second_eq _)

section Measures

variable [IsTopologicalGroup G]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace W] [BorelSpace W]
  [MeasurableSpace (W.subgroupOf U₂)] [BorelSpace (W.subgroupOf U₂)]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μL : Measure (W.subgroupOf U₂))
  (T : OpenSubgroup U₂) (C : OpenSubgroup (W.subgroupOf U₂))

/-- Normalize the independent second-complement measure by local compact-open
volumes, then transport it to `W`. No quotient measure enters the definition. -/
def secondNormalizedFactor : Measure W :=
  Measure.map D.secondComplementEquiv
    (compactOpenFactorMeasure (U₁.subgroupOf U₂) (W.subgroupOf U₂)
      μU₂ μI₂₁ μL T C)

instance secondNormalizedFactor_regular [μL.Regular] :
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C).Regular :=
  Measure.Regular.map D.secondComplementEquiv.toHomeomorph

instance secondNormalizedFactor_sFinite [SFinite μL] :
    SFinite (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) := by
  unfold secondNormalizedFactor
  infer_instance

instance secondNormalizedFactor_isMulRightInvariant [IsMulRightInvariant μL] :
    IsMulRightInvariant (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) :=
  QuotientIntegration.isMulRightInvariant_map D.secondComplementEquiv _

theorem secondNormalizedFactor_isHaarMeasure
    [T2Space G] [IsHaarMeasure μU₂] [IsHaarMeasure μI₂₁] [IsHaarMeasure μL]
    (hI : IsClosed (U₁.subgroupOf U₂ : Set U₂))
    (hT : IsCompact (T : Set U₂)) (hC : IsCompact (C : Set (W.subgroupOf U₂))) :
    IsHaarMeasure (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) := by
  let := compactOpenFactorMeasure_isHaarMeasure (U₁.subgroupOf U₂)
    (W.subgroupOf U₂) μU₂ μI₂₁ μL T C hI hT hC
  exact D.secondComplementEquiv.isHaarMeasure_map _

section LocalProduct

variable [T2Space G] [LocallyCompactSpace U₂]
  [IsHaarMeasure μU₂] [μU₂.Regular]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μL] [μL.Regular] [IsMulRightInvariant μL]
  [BorelSpace ((U₁.subgroupOf U₂) × W)]
  [BorelSpace ((U₁.subgroupOf U₂) × (W.subgroupOf U₂))]
  [SFinite μI₂₁] [SFinite μL] [(μI₂₁.prod μL).Regular]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  {ν₂₁ : Measure (QuotientSpace (U := U₁) U₂)}

/-- Local geometry and compatible Weil integration derive the second product
identity for the explicitly constructed complement measure. -/
theorem measurePreserving_second_of_localProduct
    (hν₂₁ : IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
    (hI : IsClosed (U₁.subgroupOf U₂ : Set U₂))
    (hT : IsCompact (T : Set U₂)) (hC : IsCompact (C : Set (W.subgroupOf U₂)))
    (hprod : D.secondSubgroupProduct ''
      ({h : U₁.subgroupOf U₂ | (h : U₂) ∈ T} ×ˢ
        (C : Set (W.subgroupOf U₂))) = (T : Set U₂)) :
    MeasurePreserving D.second
      (μI₂₁.prod (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)) μU₂ := by
  have hp := hν₂₁.measurePreserving_compactOpenFactorProductMeasure
    (U₁.subgroupOf U₂) (W.subgroupOf U₂) μU₂ μI₂₁ μL T C
    D.secondSubgroupProduct D.secondSubgroupProduct_eq hI hT hC hprod
  refine ⟨D.second.continuous.measurable, ?_⟩
  unfold secondNormalizedFactor
  have ht := Measure.map_prod_map (f := (id : (U₁.subgroupOf U₂) → _))
    (g := D.secondComplementEquiv) μI₂₁
    (compactOpenFactorMeasure (U₁.subgroupOf U₂) (W.subgroupOf U₂)
      μU₂ μI₂₁ μL T C) measurable_id (by fun_prop)
  simp only [Measure.map_id] at ht
  rw [ht, Measure.map_map (by fun_prop) (by fun_prop)]
  exact hp.map_eq

end LocalProduct

end Measures

section IntersectionInvariance

variable [IsTopologicalGroup G]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))

instance intersectionKernelMeasure_isMulRightInvariant [IsMulRightInvariant μH] :
    IsMulRightInvariant (D.intersectionKernelMeasure μH) :=
  QuotientIntegration.isMulRightInvariant_map D.intersectionKernelEquiv μH

instance intersectionNormalizedFactor_isMulRightInvariant [IsMulRightInvariant μK] :
    IsMulRightInvariant (D.intersectionNormalizedFactor μI₂₁ μH μK S B) :=
  QuotientIntegration.isMulRightInvariant_map D.intersectionComplementEquiv _

end IntersectionInvariance

section Composition

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
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
  [BorelSpace ((U₀.subgroupOf U₂) × V)]
  [BorelSpace (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ×
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace ((U₁.subgroupOf U₂) × W)]
  [BorelSpace ((U₁.subgroupOf U₂) × (W.subgroupOf U₂))]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μL : Measure (W.subgroupOf U₂))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (T : OpenSubgroup U₂) (C : OpenSubgroup (W.subgroupOf U₂))
  [IsHaarMeasure μU₂] [μU₂.Regular]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁] [SFinite μI₂₁]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH] [SFinite μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK] [SFinite μK]
  [IsHaarMeasure μL] [μL.Regular] [IsMulRightInvariant μL] [SFinite μL]
  [(μH.prod μK).Regular] [(μI₂₁.prod μL).Regular]
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

include hU₀ hU₁ hU₂ hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ in
/-- Both target product identities are derived from the two local compact-open
geometries. The endpoint kernel and both complements use constructed measures. -/
theorem measurePreserving_normalizedProducts :
    MeasurePreserving D.second
      (μI₂₁.prod (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)) μU₂ ∧
    MeasurePreserving D.composite
      ((D.intersectionKernelMeasure μH).prod
        ((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
          (D.secondNormalizedFactor μU₂ μI₂₁ μL T C))) μU₂ := by
  let : LocallyCompactSpace U₂ := hU₂.locallyCompactSpace
  have hI : IsClosed (U₁.subgroupOf U₂ : Set U₂) :=
    hU₁.preimage (continuous_subtype_val : Continuous (Subtype.val : U₂ → G))
  let : LocallyCompactSpace (U₁.subgroupOf U₂) := hI.locallyCompactSpace
  have hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)) :=
    hU₀.preimage
      ((continuous_subtype_val : Continuous (Subtype.val : U₂ → G)).comp
        (continuous_subtype_val :
          Continuous (Subtype.val : (U₁.subgroupOf U₂) → U₂)))
  have ha := D.measurePreserving_intersectionFirst_of_localProduct
    μI₂₁ μH μK S B hνH hH hS hB hlocal₁
  have hb := D.measurePreserving_second_of_localProduct
    μU₂ μI₂₁ μL T C hν₂₁ hI hT hC hlocal₂
  exact ⟨hb, D.measurePreserving_composite_of_intersection ha hb⟩

section Quotient

variable [BorelSpace (V × W)]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [IsFiniteMeasureOnCompacts μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀] [SFinite μI₁₀]
  [((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)).Regular]
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hν₂₀ : IsCompatible (U₀.subgroupOf U₂) μU₂
    (D.intersectionKernelMeasure μH) ν₂₀)
  (hfirst : MeasurePreserving D.first
    (μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)) μU₁)

include hU₀ hU₁ hU₂ hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ hν₁₀ hν₂₀ hfirst in
/-- The actual quotient coordinates preserve the constructed measures.
Only the original first chart still has a prescribed product identity. -/
theorem measurePreserving_quotientCoordinates_of_localProducts :
    MeasurePreserving D.quotientCoordinates.first
      (D.intersectionNormalizedFactor μI₂₁ μH μK S B) ν₁₀ ∧
    MeasurePreserving D.quotientCoordinates.second
      (D.secondNormalizedFactor μU₂ μI₂₁ μL T C) ν₂₁ ∧
    MeasurePreserving D.quotientCoordinates.composite
      ((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
        (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)) ν₂₀ := by
  obtain ⟨hb, hc⟩ := D.measurePreserving_normalizedProducts
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂
  exact D.measurePreserving_quotientCoordinates hU₀ hU₁ hU₂ μU₁ μU₂
    μI₁₀ μI₂₁ (D.intersectionKernelMeasure μH)
    (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)
    ν₁₀ ν₂₁ ν₂₀ hν₁₀ hν₂₁ hν₂₀ hfirst hb hc

end Quotient

end Composition

section Integral

variable [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
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
  [BorelSpace ((U₀.subgroupOf U₂) × V)]
  [BorelSpace (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ×
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace ((U₁.subgroupOf U₂) × W)]
  [BorelSpace ((U₁.subgroupOf U₂) × (W.subgroupOf U₂))]
  (μU₂ : Measure U₂) (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μL : Measure (W.subgroupOf U₂))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (T : OpenSubgroup U₂) (C : OpenSubgroup (W.subgroupOf U₂))
  [IsHaarMeasure μU₂] [μU₂.Regular]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁] [SFinite μI₂₁]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH] [SFinite μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK] [SFinite μK]
  [IsHaarMeasure μL] [μL.Regular] [IsMulRightInvariant μL] [SFinite μL]
  [(μH.prod μK).Regular] [(μI₂₁.prod μL).Regular]
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


variable [BorelSpace (V × W)]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [IsFiniteMeasureOnCompacts μU₁]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀] [SFinite μI₁₀]
  [((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)).Regular]
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hν₂₀ : IsCompatible (U₀.subgroupOf U₂) μU₂
    (D.intersectionKernelMeasure μH) ν₂₀)
  (hfirst : MeasurePreserving D.first
    (μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)) μU₁)


variable
  {P₀ P₁ M : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

include hU₂ hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ hν₁₀ hν₂₀ hfirst in
/-- Actual standard-integral composition after deriving the second and
composite normalizations from local compact-open product geometry. -/
theorem comp_hasIntegral_of_localProducts
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
  obtain ⟨hc₁₀, hc₂₁, hc₂₀⟩ := D.measurePreserving_quotientCoordinates_of_localProducts
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ μU₁ μI₁₀ ν₁₀ ν₂₀
    hν₁₀ hν₂₀ hfirst
  exact hf.comp_ordered h₀ hU₀ h₁ hU₁ A D.quotientCoordinates
    (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)
    ν₁₀ ν₂₁ ν₂₀ hc₁₀ hc₂₁ hc₂₀ hF ha

end Integral

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
