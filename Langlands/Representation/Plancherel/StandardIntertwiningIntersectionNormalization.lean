import Langlands.Analysis.Local.CompactOpenFactorProduct
import Langlands.Representation.Plancherel.StandardIntertwiningIntersectionFactorization

/-! # Local normalization of the actual intermediate intersection factors -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)


/-- Identify the actual endpoint intersection inside the middle intersection
with its original carrier. Its containment is a consequence of the three charts. -/
def intersectionKernelEquiv : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ≃ₜ* (U₀.subgroupOf U₂) :=
  subgroupOfContinuousEquiv (by
    intro g hg
    exact D.intersection_le_middle ⟨hg, g.property⟩)

/-- Identify the actual complementary subgroup inside the middle intersection
with the original complementary group. -/
def intersectionComplementEquiv : ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ≃ₜ* V :=
  (subgroupOfContinuousEquiv (by
    intro g hg
    exact D.first_le hg)).trans (subgroupOfContinuousEquiv D.first_le_target)

/-- Literal multiplication on two actual subgroups of the middle intersection.
This is an ordered homeomorphism, without a product homomorphism assertion. -/
def intersectionSubgroupProduct : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) × ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ≃ₜ (U₁.subgroupOf U₂) :=
  (D.intersectionKernelEquiv.toHomeomorph.prodCongr
    D.intersectionComplementEquiv.toHomeomorph).trans D.intersectionFirst

/-- The transported chart is actual multiplication in the middle intersection. -/
theorem intersectionSubgroupProduct_eq (p : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) × ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) :
    D.intersectionSubgroupProduct p = p.1.val * p.2.val := by
  apply Subtype.ext
  exact D.intersectionFirst_eq _

section Measures

variable [IsTopologicalGroup G]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  (μI₂₁ : Measure (U₁.subgroupOf U₂)) (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (S : OpenSubgroup (U₁.subgroupOf U₂)) (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))

/-- Transport an independently supplied Haar measure on the actual nested
intersection; this does not restrict the ambient measure to that subgroup. -/
def intersectionKernelMeasure : Measure (U₀.subgroupOf U₂) :=
  Measure.map D.intersectionKernelEquiv μH

/-- Normalize the actual complementary subgroup by compact-open volumes,
then transport that measure to the original complement carrier. -/
def intersectionNormalizedFactor : Measure V :=
  Measure.map D.intersectionComplementEquiv
    (compactOpenFactorMeasure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) μI₂₁ μH μK S B)

instance intersectionKernelMeasure_regular [μH.Regular] :
    (D.intersectionKernelMeasure μH).Regular :=
  Measure.Regular.map D.intersectionKernelEquiv.toHomeomorph

instance intersectionKernelMeasure_isHaarMeasure [IsHaarMeasure μH] :
    IsHaarMeasure (D.intersectionKernelMeasure μH) :=
  D.intersectionKernelEquiv.isHaarMeasure_map μH

instance intersectionKernelMeasure_sFinite [SFinite μH] :
    SFinite (D.intersectionKernelMeasure μH) := by
  unfold intersectionKernelMeasure
  infer_instance

instance intersectionNormalizedFactor_regular [μK.Regular] :
    (D.intersectionNormalizedFactor μI₂₁ μH μK S B).Regular :=
  Measure.Regular.map D.intersectionComplementEquiv.toHomeomorph

instance intersectionNormalizedFactor_sFinite [SFinite μK] :
    SFinite (D.intersectionNormalizedFactor μI₂₁ μH μK S B) := by
  unfold intersectionNormalizedFactor
  infer_instance

omit [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)] in
/-- The explicitly normalized factor is Haar after transport to `V`. -/
theorem intersectionNormalizedFactor_isHaarMeasure
    [T2Space G] [IsHaarMeasure μI₂₁] [IsHaarMeasure μH] [IsHaarMeasure μK]
    (hH : IsClosed (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) : Set (U₁.subgroupOf U₂)))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂))) (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) :
    IsHaarMeasure (D.intersectionNormalizedFactor μI₂₁ μH μK S B) := by
  let := compactOpenFactorMeasure_isHaarMeasure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) μI₂₁ μH μK S B hH hS hB
  exact D.intersectionComplementEquiv.isHaarMeasure_map _


section LocalProduct

variable [T2Space G] [LocallyCompactSpace (U₁.subgroupOf U₂)]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular]
  [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK]
  [BorelSpace ((U₀.subgroupOf U₂) × V)]
  [BorelSpace (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) × ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))] [SFinite μH] [SFinite μK]
  [(μH.prod μK).Regular]
  [MeasurableSpace (LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))] [BorelSpace (LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  {ν : Measure (LeftQuotient ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))}

/-- Local compact-open product geometry gives exact normalization of the
restricted first chart in the original factor carriers. -/
theorem measurePreserving_intersectionFirst_of_localProduct
    (hν : IsCompatible ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) μI₂₁ μH ν)
    (hH : IsClosed (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) : Set (U₁.subgroupOf U₂)))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂))) (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hprod : D.intersectionSubgroupProduct ''
      ({h : ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) | (h : (U₁.subgroupOf U₂)) ∈ S} ×ˢ (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) = (S : Set (U₁.subgroupOf U₂))) :
    MeasurePreserving D.intersectionFirst
      ((D.intersectionKernelMeasure μH).prod
        (D.intersectionNormalizedFactor μI₂₁ μH μK S B)) μI₂₁ := by
  have hp := hν.measurePreserving_compactOpenFactorProductMeasure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    μI₂₁ μH μK S B D.intersectionSubgroupProduct D.intersectionSubgroupProduct_eq
    hH hS hB hprod
  refine ⟨D.intersectionFirst.continuous.measurable, ?_⟩
  unfold intersectionKernelMeasure intersectionNormalizedFactor
  rw [Measure.map_prod_map (f := D.intersectionKernelEquiv)
      (g := D.intersectionComplementEquiv) _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact hp.map_eq


end LocalProduct

end Measures

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
