import Langlands.Representation.Plancherel.StandardIntertwiningFirstFactorMass

/-! # Compact-open compatibility for the actual first complement -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- The two actual subgroup copies of the first complement are continuously
group-isomorphic, preserving their underlying elements in `G`. -/
def firstComplementCopiesEquiv :
    V.subgroupOf U₁ ≃ₜ* ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :=
  D.firstComplementEquiv.trans D.intersectionComplementEquiv.symm

/-- Use the same compact open subgroup in the two actual complement copies. -/
def firstCompactComplement
    (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) :
    OpenSubgroup (V.subgroupOf U₁) :=
  B.comap D.firstComplementCopiesEquiv.toMonoidHom
    D.firstComplementCopiesEquiv.continuous

theorem firstCompactComplement_isCompact
    (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) :
    IsCompact (D.firstCompactComplement B : Set (V.subgroupOf U₁)) :=
  D.firstComplementCopiesEquiv.toHomeomorph.isCompact_preimage.mpr hB

section Mass

variable [IsTopologicalGroup G]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))

omit [IsTopologicalGroup G] [BorelSpace (U₁.subgroupOf U₂)]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] in
/-- The first compact-open mass is precisely the mass used to construct
the normalized intersection factor. -/
theorem firstCompactComplement_mass :
    D.firstComplementMeasure (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
        (D.firstCompactComplement B : Set (V.subgroupOf U₁)) =
      compactOpenFactorMeasure
        ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
        ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
        μI₂₁ μH μK S B
        (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))) := by
  rw [firstComplementMeasure, intersectionNormalizedFactor,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop)
      (D.firstCompactComplement B).isOpen.measurableSet]
  congr 1

/-- The constructed mass obeys the intersection chart's compact-open volume
equation, now on the actual first-complement copy. -/
theorem firstCompactComplement_volume
    [T2Space G] [IsHaarMeasure μI₂₁] [IsHaarMeasure μH] [IsHaarMeasure μK]
    (hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))) :
    μI₂₁ (S : Set (U₁.subgroupOf U₂)) =
      μH {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
        (h : U₁.subgroupOf U₂) ∈ S} *
      D.firstComplementMeasure (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
        (D.firstCompactComplement B : Set (V.subgroupOf U₁)) := by
  rw [D.firstCompactComplement_mass μI₂₁ μH μK S B]
  exact compactOpenFactorMeasure_mass
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    μI₂₁ μH μK S B hH hS hB

/-- Unit mass on the middle compact open and its kernel fixes unit mass on
the transported first compact complement, independently of the seed scale. -/
theorem firstCompactComplement_mass_one
    [T2Space G] [IsHaarMeasure μI₂₁] [IsHaarMeasure μH] [IsHaarMeasure μK]
    (hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)))
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (hSmass : μI₂₁ (S : Set (U₁.subgroupOf U₂)) = 1)
    (hHmass : μH {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
      (h : U₁.subgroupOf U₂) ∈ S} = 1) :
    D.firstComplementMeasure (D.intersectionNormalizedFactor μI₂₁ μH μK S B)
      (D.firstCompactComplement B : Set (V.subgroupOf U₁)) = 1 := by
  have hm := D.firstCompactComplement_volume μI₂₁ μH μK S B hH hS hB
  simpa only [hSmass, hHmass, one_mul] using hm.symm

end Mass

section First

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
/-- Unit normalization of the ambient and kernel compact opens derives the
first product identity. The factor measure is the existing constructed one. -/
theorem measurePreserving_first_of_unitCompactOpens
    (hν₁₀ : IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
    (hS : IsCompact (S : Set (U₁.subgroupOf U₂)))
    (hB : IsCompact (B : Set ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))))
    (R : OpenSubgroup U₁) (hR : IsCompact (R : Set U₁))
    (hlocal : D.firstSubgroupProduct ''
      ({h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} ×ˢ
        (D.firstCompactComplement B : Set (V.subgroupOf U₁))) = (R : Set U₁))
    (hRmass : μU₁ (R : Set U₁) = 1)
    (hI₁₀mass : μI₁₀ {h : U₀.subgroupOf U₁ | (h : U₁) ∈ R} = 1)
    (hSmass : μI₂₁ (S : Set (U₁.subgroupOf U₂)) = 1)
    (hHmass : μH {h : (U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂) |
      (h : U₁.subgroupOf U₂) ∈ S} = 1) :
    MeasurePreserving D.first
      (μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)) μU₁ := by
  have hH : IsClosed
      (((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) :
        Set (U₁.subgroupOf U₂)) :=
    hU₀.preimage
      ((continuous_subtype_val : Continuous (Subtype.val : U₂ → G)).comp
        (continuous_subtype_val :
          Continuous (Subtype.val : (U₁.subgroupOf U₂) → U₂)))
  have hmass := D.firstCompactComplement_mass_one μI₂₁ μH μK S B
    hH hS hB hSmass hHmass
  apply D.measurePreserving_first_normalized_of_compactOpenMass
    hU₀ hU₁ μU₁ μI₁₀ μI₂₁ μH μK S B hν₁₀ hS hB R hR
    (D.firstCompactComplement B) (D.firstCompactComplement_isCompact B hB) hlocal
  rw [hRmass, hI₁₀mass, hmass, one_mul]

end First

section Integral

open Induction

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
  [IsHaarMeasure μU₁] [μU₁.Regular]
  [MeasurableSpace (V.subgroupOf U₁)] [BorelSpace (V.subgroupOf U₁)]
  [BorelSpace ((U₀.subgroupOf U₁) × V)]
  [BorelSpace ((U₀.subgroupOf U₁) × (V.subgroupOf U₁))]
  [(μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)).Regular]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀] [SFinite μI₁₀]
  [((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
    (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)).Regular]
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

include hU₂ hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ hν₁₀ hν₂₀
  hR hlocal₀ hRmass hI₁₀mass hSmass hHmass in
/-- Actual standard-integral composition with all three global product
normalizations derived from local geometry and unit compact-open masses. -/
theorem comp_hasIntegral_of_unitCompactOpens
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
  have hfirst := D.measurePreserving_first_of_unitCompactOpens
    hU₀ hU₁ μU₁ μI₁₀ μI₂₁ μH μK S B hν₁₀ hS hB R hR hlocal₀
    hRmass hI₁₀mass hSmass hHmass
  exact D.comp_hasIntegral_of_localProducts
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ μU₁ μI₁₀ ν₁₀ ν₂₀
    hν₁₀ hν₂₀ hfirst h₀ h₁ A hf hF ha

end Integral

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
