import Langlands.Analysis.Local.QuotientFactorization
import Langlands.Representation.Plancherel.StandardIntertwiningComposition

/-! # Standard-integral coordinates from literal subgroup factorizations -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}

/-- Literal ordered product coordinates in the actual target subgroups.
The factors need not commute or be normal. Their existence is a separate
geometric obligation. -/
structure OrderedSubgroupFactorization
    (U₀ U₁ U₂ V W : Subgroup G) where
  first_le : V ≤ U₁
  first_le_target : V ≤ U₂
  second_le : W ≤ U₂
  first : (U₀.subgroupOf U₁) × V ≃ₜ U₁
  second : (U₁.subgroupOf U₂) × W ≃ₜ U₂
  composite : (U₀.subgroupOf U₂) × (V × W) ≃ₜ U₂
  first_eq (p : (U₀.subgroupOf U₁) × V) :
    first p = p.1.val * Subgroup.inclusion first_le p.2
  second_eq (p : (U₁.subgroupOf U₂) × W) :
    second p = p.1.val * Subgroup.inclusion second_le p.2
  composite_eq (p : (U₀.subgroupOf U₂) × (V × W)) :
    composite p = p.1.val *
      (Subgroup.inclusion first_le_target p.2.1 * Subgroup.inclusion second_le p.2.2)

namespace OrderedSubgroupFactorization

variable [IsTopologicalGroup G]
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [BorelSpace (V × W)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]

/-- Construct all three actual measurable coset charts from the literal
product homeomorphisms, rather than supplying quotient equivalences. -/
def quotientCoordinates : OrderedQuotientCoordinates U₀ U₁ U₂ V W where
  first_le := D.first_le
  first_le_target := D.first_le_target
  second_le := D.second_le
  first := (QuotientIntegration.factorQuotientHomeomorph (U₀.subgroupOf U₁)
    (Subgroup.inclusion D.first_le) D.first D.first_eq).toMeasurableEquiv
  second := (QuotientIntegration.factorQuotientHomeomorph (U₁.subgroupOf U₂)
    (Subgroup.inclusion D.second_le) D.second D.second_eq).toMeasurableEquiv
  composite := (QuotientIntegration.factorQuotientHomeomorph (U₀.subgroupOf U₂)
    (fun p : V × W =>
      Subgroup.inclusion D.first_le_target p.1 * Subgroup.inclusion D.second_le p.2)
    D.composite D.composite_eq).toMeasurableEquiv
  first_eq _ := rfl
  second_eq _ := rfl
  composite_eq _ := rfl

section Measures

variable [T2Space G] [LocallyCompactSpace G]
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  (μU₁ : Measure U₁) (μU₂ : Measure U₂)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μI₂₀ : Measure (U₀.subgroupOf U₂))
  (μV : Measure V) (μW : Measure W)
  [IsFiniteMeasureOnCompacts μU₁] [IsFiniteMeasureOnCompacts μU₂]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μI₂₀] [μI₂₀.Regular] [IsMulRightInvariant μI₂₀]
  [SFinite μI₁₀] [SFinite μI₂₁] [SFinite μI₂₀]
  [SFinite μV] [SFinite μW]
  [μV.Regular] [μW.Regular] [(μV.prod μW).Regular]
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hν₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hν₂₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
  (hν₂₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₂) μU₂ μI₂₀ ν₂₀)
  (hprod₁₀ : MeasurePreserving D.first (μI₁₀.prod μV) μU₁)
  (hprod₂₁ : MeasurePreserving D.second (μI₂₁.prod μW) μU₂)
  (hprod₂₀ : MeasurePreserving D.composite (μI₂₀.prod (μV.prod μW)) μU₂)

include hU₀ hU₁ hU₂ hν₁₀ hν₂₁ hν₂₀ hprod₁₀ hprod₂₁ hprod₂₀ in
/-- Derive the three exact quotient normalizations from compatible Weil
measures and the ambient product identities. The two target products share
the same supplied measure on `U₂`. -/
theorem measurePreserving_quotientCoordinates :
    MeasurePreserving D.quotientCoordinates.first μV ν₁₀ ∧
    MeasurePreserving D.quotientCoordinates.second μW ν₂₁ ∧
    MeasurePreserving D.quotientCoordinates.composite (μV.prod μW) ν₂₀ := by
  let : LocallyCompactSpace U₁ := hU₁.locallyCompactSpace
  let : LocallyCompactSpace U₂ := hU₂.locallyCompactSpace
  have hI₁₀ : IsClosed (U₀.subgroupOf U₁ : Set U₁) :=
    hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : U₁ → G))
  have hI₂₁ : IsClosed (U₁.subgroupOf U₂ : Set U₂) :=
    hU₁.preimage (continuous_subtype_val : Continuous (Subtype.val : U₂ → G))
  have hI₂₀ : IsClosed (U₀.subgroupOf U₂ : Set U₂) :=
    hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : U₂ → G))
  exact ⟨hν₁₀.measurePreserving_factorQuotientHomeomorph _ _ _ D.first_eq hI₁₀ hprod₁₀,
    hν₂₁.measurePreserving_factorQuotientHomeomorph _ _ _ D.second_eq hI₂₁ hprod₂₁,
    hν₂₀.measurePreserving_factorQuotientHomeomorph _ _ _ D.composite_eq hI₂₀ hprod₂₀⟩

end Measures

end OrderedSubgroupFactorization

namespace OrderedSubgroupFactorization

section Integral

variable [NonarchimedeanGroup G] [T2Space G] [LocallyCompactSpace G]
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)
  (hU₀ : IsClosed (U₀ : Set G)) (hU₁ : IsClosed (U₁ : Set G))
  (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
  [BorelSpace (V × W)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  (μU₁ : Measure U₁) (μU₂ : Measure U₂)
  (μI₁₀ : Measure (U₀.subgroupOf U₁))
  (μI₂₁ : Measure (U₁.subgroupOf U₂))
  (μI₂₀ : Measure (U₀.subgroupOf U₂))
  (μV : Measure V) (μW : Measure W)
  [IsFiniteMeasureOnCompacts μU₁] [IsFiniteMeasureOnCompacts μU₂]
  [IsHaarMeasure μI₁₀] [μI₁₀.Regular] [IsMulRightInvariant μI₁₀]
  [IsHaarMeasure μI₂₁] [μI₂₁.Regular] [IsMulRightInvariant μI₂₁]
  [IsHaarMeasure μI₂₀] [μI₂₀.Regular] [IsMulRightInvariant μI₂₀]
  [SFinite μI₁₀] [SFinite μI₂₁] [SFinite μI₂₀]
  [SFinite μV] [SFinite μW]
  [μV.Regular] [μW.Regular] [(μV.prod μW).Regular]
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))
  (hν₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hν₂₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
  (hν₂₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₂) μU₂ μI₂₀ ν₂₀)
  (hprod₁₀ : MeasurePreserving D.first (μI₁₀.prod μV) μU₁)
  (hprod₂₁ : MeasurePreserving D.second (μI₂₁.prod μW) μU₂)
  (hprod₂₀ : MeasurePreserving D.composite (μI₂₀.prod (μV.prod μW)) μU₂)
  {P₀ P₁ M : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀)
  (h₁ : IsSemidirectDecomposition P₁ M U₁)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

include D hU₂ hν₁₀ hν₂₁ hν₂₀ hprod₁₀ hprod₂₁ hprod₂₀ in
/-- Apply actual standard-integral composition using only literal product
factorizations and their ambient normalizations as coordinate inputs. -/
theorem comp_hasIntegral
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f) :
    HasIntegral h₀ hU₀ U₂ A ν₂₀ f J := by
  obtain ⟨hc₁₀, hc₂₁, hc₂₀⟩ := D.measurePreserving_quotientCoordinates
    hU₀ hU₁ hU₂ μU₁ μU₂ μI₁₀ μI₂₁ μI₂₀ μV μW ν₁₀ ν₂₁ ν₂₀
    hν₁₀ hν₂₁ hν₂₀ hprod₁₀ hprod₂₁ hprod₂₀
  exact hf.comp_ordered h₀ hU₀ h₁ hU₁ A D.quotientCoordinates μV μW ν₁₀ ν₂₁ ν₂₀
    hc₁₀ hc₂₁ hc₂₀ hF ha

end Integral

end OrderedSubgroupFactorization

end Langlands.Plancherel.StandardIntertwining
