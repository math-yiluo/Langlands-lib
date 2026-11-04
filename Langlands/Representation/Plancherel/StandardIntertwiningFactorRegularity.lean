import Langlands.Representation.Plancherel.StandardIntertwiningFactorChoice
import Langlands.Representation.Plancherel.StandardIntertwiningCompactOpenComposition

/-! # Seed-product regularity for normalized standard-intertwining factors -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

open Aubert.General QuotientIntegration

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

/-- Identify the ordered pair of actual seed subgroup copies with the original
complement carriers. This map does not multiply the two factors in `G`. -/
def normalizedComplementProductHomeomorph :
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) ×
      (W.subgroupOf U₂) ≃ₜ V × W :=
  D.intersectionComplementEquiv.toHomeomorph.prodCongr
    D.secondComplementEquiv.toHomeomorph

section FirstProduct

variable [IsTopologicalGroup G]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [MeasurableSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  [BorelSpace ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))]
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μH : Measure ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (μK : Measure ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  (S : OpenSubgroup (U₁.subgroupOf U₂))
  (B : OpenSubgroup ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))
  [BorelSpace ((U₀.subgroupOf U₁) ×
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [BorelSpace ((U₀.subgroupOf U₁) × V)]

/-- A genuine seed-product regularity hypothesis suffices for the first chart's
constructed product. No local product or Haar normalization identity is needed. -/
instance intersectionNormalizedFactor_prod_regular
    [SFinite μI₁₀] [SFinite μK] [(μI₁₀.prod μK).Regular] :
    (μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B)).Regular := by
  let e := (Homeomorph.refl (U₀.subgroupOf U₁)).prodCongr
    D.intersectionComplementEquiv.toHomeomorph
  let κ := compactOpenFactorMeasure
    ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
    μI₂₁ μH μK S B
  have ht : μI₁₀.prod (D.intersectionNormalizedFactor μI₂₁ μH μK S B) =
      Measure.map e (μI₁₀.prod κ) := by
    change μI₁₀.prod (Measure.map D.intersectionComplementEquiv κ) =
      Measure.map (Prod.map id D.intersectionComplementEquiv) (μI₁₀.prod κ)
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (f := (id : (U₀.subgroupOf U₁) → _))
        (g := D.intersectionComplementEquiv) μI₁₀ κ measurable_id (by fun_prop))
  have : (μI₁₀.prod κ).Regular := by
    dsimp [κ, compactOpenFactorMeasure]
    rw [Measure.prod_smul_right]
    infer_instance
  rw [ht]
  exact Measure.Regular.map e

end FirstProduct

section ComplementProduct

variable [IsTopologicalGroup G]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
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

omit [IsTopologicalGroup G] [BorelSpace U₂] [BorelSpace (U₁.subgroupOf U₂)]
  [BorelSpace ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))] in
/-- The normalized complement product is exactly the pushforward of the two
scaled seed measures by the product of the canonical subgroup equivalences. -/
theorem normalizedComplementProductMeasure_eq_map
    [SFinite μK] [SFinite μL] :
    D.normalizedComplementProductMeasure μU₂ μI₂₁ μH μK μL S B T C =
      Measure.map D.normalizedComplementProductHomeomorph
        ((compactOpenFactorMeasure
          ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
          ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
          μI₂₁ μH μK S B).prod
            (compactOpenFactorMeasure (U₁.subgroupOf U₂) (W.subgroupOf U₂)
              μU₂ μI₂₁ μL T C)) := by
  unfold normalizedComplementProductMeasure intersectionNormalizedFactor
    secondNormalizedFactor normalizedComplementProductHomeomorph
  exact Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)

variable [BorelSpace
    (((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) × (W.subgroupOf U₂))]
  [BorelSpace (V × W)]

/-- Regularity of the actual seed product transports to the ordered product
used for standard-intertwining scalar Fubini. Both scalars are finite NNReal. -/
instance normalizedComplementProduct_regular
    [SFinite μK] [SFinite μL] [(μK.prod μL).Regular] :
    ((D.intersectionNormalizedFactor μI₂₁ μH μK S B).prod
      (D.secondNormalizedFactor μU₂ μI₂₁ μL T C)).Regular := by
  change (D.normalizedComplementProductMeasure μU₂ μI₂₁ μH μK μL S B T C).Regular
  rw [D.normalizedComplementProductMeasure_eq_map μU₂ μI₂₁ μH μK μL S B T C]
  have : ((compactOpenFactorMeasure
      ((U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂))
      μI₂₁ μH μK S B).prod
        (compactOpenFactorMeasure (U₁.subgroupOf U₂) (W.subgroupOf U₂)
          μU₂ μI₂₁ μL T C)).Regular := by
    unfold compactOpenFactorMeasure
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
    infer_instance
  exact Measure.Regular.map D.normalizedComplementProductHomeomorph

end ComplementProduct

section IntegralFromSeedRegularity

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
  [BorelSpace ((U₀.subgroupOf U₁) ×
    ((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)))]
  [(μI₁₀.prod μK).Regular]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀] [SFinite μI₁₀]
  [BorelSpace
    (((V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)) × (W.subgroupOf U₂))]
  [(μK.prod μL).Regular]
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
/-- Actual standard-integral composition with constructed-product regularity
derived from seed-product regularity, and all global product normalizations
derived from local geometry and the four genuine unit compact-open masses. -/
theorem comp_hasIntegral_of_seedRegularity
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
  exact D.comp_hasIntegral_of_unitCompactOpens
    hU₀ hU₁ hU₂ μU₂ μI₂₁ μH μK μL S B T C νH ν₂₁
    hνH hν₂₁ hS hB hlocal₁ hT hC hlocal₂ μU₁ μI₁₀ ν₁₀ ν₂₀
    hν₁₀ hν₂₀ R hR hlocal₀ hRmass hI₁₀mass hSmass hHmass h₀ h₁ A hf hF ha

end IntegralFromSeedRegularity

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization
