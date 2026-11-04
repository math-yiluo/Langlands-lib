import Langlands.Representation.Plancherel.StandardIntertwiningLocallyNormalizedComposition

/-! # First-chart normalization from a concrete compact-open mass comparison -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- Identify the actual first complement in `U₁` with its original carrier. -/
def firstComplementEquiv : V.subgroupOf U₁ ≃ₜ* V :=
  subgroupOfContinuousEquiv D.first_le

/-- The first chart expressed as multiplication of actual subgroups of `U₁`. -/
def firstSubgroupProduct : (U₀.subgroupOf U₁) × (V.subgroupOf U₁) ≃ₜ U₁ :=
  ((Homeomorph.refl (U₀.subgroupOf U₁)).prodCongr
    D.firstComplementEquiv.toHomeomorph).trans D.first

theorem firstSubgroupProduct_eq (p : (U₀.subgroupOf U₁) × (V.subgroupOf U₁)) :
    D.firstSubgroupProduct p = p.1.val * p.2.val := by
  apply Subtype.ext
  exact congrArg (fun z : U₁ => z.val) (D.first_eq _)

section Measures

variable [IsTopologicalGroup G]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  (μV : Measure V)

/-- Transport the already specified complement measure to its actual copy
inside `U₁`. This is an inverse group-equivalence pushforward. -/
def firstComplementMeasure : Measure (V.subgroupOf U₁) :=
  Measure.map D.firstComplementEquiv.symm μV

instance firstComplementMeasure_regular [μV.Regular] :
    (D.firstComplementMeasure μV).Regular :=
  Measure.Regular.map D.firstComplementEquiv.symm.toHomeomorph

instance firstComplementMeasure_isHaarMeasure [IsHaarMeasure μV] :
    IsHaarMeasure (D.firstComplementMeasure μV) :=
  D.firstComplementEquiv.symm.isHaarMeasure_map μV

instance firstComplementMeasure_sFinite [SFinite μV] :
    SFinite (D.firstComplementMeasure μV) := by
  unfold firstComplementMeasure
  infer_instance

instance firstComplementMeasure_isMulRightInvariant [IsMulRightInvariant μV] :
    IsMulRightInvariant (D.firstComplementMeasure μV) :=
  QuotientIntegration.isMulRightInvariant_map D.firstComplementEquiv.symm μV

omit [IsTopologicalGroup G] in
/-- The return transport recovers precisely the original measure. -/
@[simp] theorem map_firstComplementMeasure :
    Measure.map D.firstComplementEquiv (D.firstComplementMeasure μV) = μV := by
  rw [firstComplementMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map id μV = μV
  exact Measure.map_id

variable [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [BorelSpace ((U₀.subgroupOf U₁) × V)]
  [BorelSpace ((U₀.subgroupOf U₁) × (V.subgroupOf U₁))]
  (μI₁₀ : Measure (U₀.subgroupOf U₁))

/-- Regularity of the original product transports through the actual product
homeomorphism; regularity of a new product need not be postulated. -/
instance firstComplementMeasure_prod_regular
    [SFinite μI₁₀] [SFinite μV] [(μI₁₀.prod μV).Regular] :
    (μI₁₀.prod (D.firstComplementMeasure μV)).Regular := by
  let e := (Homeomorph.refl (U₀.subgroupOf U₁)).prodCongr
    D.firstComplementEquiv.symm.toHomeomorph
  have ht : μI₁₀.prod (D.firstComplementMeasure μV) =
      Measure.map e (μI₁₀.prod μV) := by
    unfold firstComplementMeasure
    change μI₁₀.prod (Measure.map D.firstComplementEquiv.symm μV) =
      Measure.map (Prod.map id D.firstComplementEquiv.symm) (μI₁₀.prod μV)
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (f := (id : (U₀.subgroupOf U₁) → _))
        (g := D.firstComplementEquiv.symm) μI₁₀ μV measurable_id (by fun_prop))
  rw [ht]
  exact Measure.Regular.map e

section CompactOpen

variable [T2Space G] [LocallyCompactSpace U₁]
  [MeasurableSpace U₁] [BorelSpace U₁]
  (μU₁ : Measure U₁) [IsHaarMeasure μU₁] [μU₁.Regular]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μV] [μV.Regular] [IsMulRightInvariant μV]
  [SFinite μI₁₀] [SFinite μV] [(μI₁₀.prod μV).Regular]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  {ν₁₀ : Measure (QuotientSpace (U := U₀) U₁)}

/-- A local Cartesian product and one actual compact-open mass identity imply
the global first-chart product normalization for the specified measure. -/
theorem measurePreserving_first_of_compactOpenMass
    (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
    (hI : IsClosed (U₀.subgroupOf U₁ : Set U₁))
    (R : OpenSubgroup U₁) (hR : IsCompact (R : Set U₁))
    (A : OpenSubgroup (V.subgroupOf U₁))
    (hA : IsCompact (A : Set (V.subgroupOf U₁)))
    (hprod : D.firstSubgroupProduct ''
      ({h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} ×ˢ
        (A : Set (V.subgroupOf U₁))) = (R : Set U₁))
    (hmass : μU₁ (R : Set U₁) =
      μI₁₀ {h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} *
        D.firstComplementMeasure μV (A : Set (V.subgroupOf U₁))) :
    MeasurePreserving D.first (μI₁₀.prod μV) μU₁ := by
  have horbit := factorQuotientHomeomorph_image_of_localProduct
    (U₀.subgroupOf U₁) Subtype.val D.firstSubgroupProduct
    D.firstSubgroupProduct_eq _ _ _ ⟨1, R.one_mem⟩ hprod
  have hp := hν₁₀.measurePreserving_factorProduct_of_compactOpen
    (U₀.subgroupOf U₁) (V.subgroupOf U₁) D.firstSubgroupProduct
    D.firstSubgroupProduct_eq hI (D.firstComplementMeasure μV)
    R hR A hA horbit hmass
  refine ⟨D.first.continuous.measurable, ?_⟩
  have ht := Measure.map_prod_map (f := (id : (U₀.subgroupOf U₁) → _))
    (g := D.firstComplementEquiv) μI₁₀ (D.firstComplementMeasure μV)
    measurable_id (by fun_prop)
  simp only [Measure.map_id, map_firstComplementMeasure] at ht
  rw [ht, Measure.map_map (by fun_prop) (by fun_prop)]
  exact hp.map_eq

end CompactOpen

end Measures

section ConstructedFactor

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₁) × V)]
  [BorelSpace ((U₀.subgroupOf U₁) × (V.subgroupOf U₁))]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  [IsHaarMeasure μU₁] [μU₁.Regular]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀] [SFinite μI₁₀]
  [IsHaarMeasure μI₂₁] [IsHaarMeasure μH]
  [IsHaarMeasure μK] [μK.Regular] [IsMulRightInvariant μK] [SFinite μK]
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  [(μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)).Regular]
  {ν₁₀ : Measure (QuotientSpace (U := U₀) U₁)}

include hU₀ hU₁ in
/-- Apply the first-chart comparison to the same explicitly normalized
complement measure used by the second and composite chart construction. -/
theorem measurePreserving_first_normalized_of_compactOpenMass
    (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (R : OpenSubgroup U₁) (hR : IsCompact (R : Set U₁))
    (A : OpenSubgroup (V.subgroupOf U₁))
    (hA : IsCompact (A : Set (V.subgroupOf U₁)))
    (hprod : D.firstSubgroupProduct ''
      ({h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} ×ˢ
        (A : Set (V.subgroupOf U₁))) = (R : Set U₁))
    (hmass : μU₁ (R : Set U₁) =
      μI₁₀ {h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} *
        D.firstComplementMeasure (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
          (A : Set (V.subgroupOf U₁))) :
    MeasurePreserving D.first
      (μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)) μU₁ := by
  let : LocallyCompactSpace U₁ := hU₁.locallyCompactSpace
  have hI : IsClosed (U₀.subgroupOf U₁ : Set U₁) :=
    hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : U₁ → G))
  have hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)) :=
    hU₀.preimage
      ((continuous_subtype_val : Continuous (Subtype.val : U₂ → G)).comp
        (continuous_subtype_val :
          Continuous (Subtype.val : (U₁.subgroupOf U₂) → U₂)))
  let := D.intersectionNormalizedFactor_isHaarMeasure μI₂₁ μH μK S B hH hS hB
  exact D.measurePreserving_first_of_compactOpenMass
    (D.intersectionNormalizedFactor μI₂₁ μH μK S B) μI₁₀ μU₁
    hν₁₀ hI R hR A hA hprod hmass

end ConstructedFactor

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
