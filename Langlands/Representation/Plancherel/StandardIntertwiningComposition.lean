import Langlands.Representation.Plancherel.StandardIntertwiningTargetLaws
import Langlands.HarmonicAnalysis.SmoothWeakFubini

/-! # Ordered quotient coordinates and actual standard-integral composition -/

noncomputable section

open MeasureTheory

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

section Coordinates

variable {G : Type uG} [Group G]
  (U₀ U₁ U₂ V W : Subgroup G)
  [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]

/-- Actual coset charts for the two successive integrals and their ordered
product. This is measurable data; neither commutativity nor a product group
decomposition is asserted. Existence and measure normalization remain to prove
in each application. -/
structure OrderedQuotientCoordinates where
  first_le : V ≤ U₁
  first_le_target : V ≤ U₂
  second_le : W ≤ U₂
  first : V ≃ᵐ QuotientSpace (U := U₀) U₁
  second : W ≃ᵐ QuotientSpace (U := U₁) U₂
  composite : V × W ≃ᵐ QuotientSpace (U := U₀) U₂
  first_eq (v : V) :
    first v = Quotient.mk _ (Subgroup.inclusion first_le v)
  second_eq (w : W) :
    second w = Quotient.mk _ (Subgroup.inclusion second_le w)
  composite_eq (p : V × W) :
    composite p = Quotient.mk _
      (Subgroup.inclusion first_le_target p.1 * Subgroup.inclusion second_le p.2)

end Coordinates

section Integral

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ U₂ V W : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace V] [MeasurableSpace W]
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)]
  (C : OrderedQuotientCoordinates U₀ U₁ U₂ V W)
  (μV : Measure V) (μW : Measure W)
  (ν₁₀ : Measure (QuotientSpace (U := U₀) U₁))
  (ν₂₁ : Measure (QuotientSpace (U := U₁) U₂))
  (ν₂₀ : Measure (QuotientSpace (U := U₀) U₂))

omit h₁ hU₁ C ν₁₀ ν₂₁ ν₂₀
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]
  [MeasurableSpace (QuotientSpace (U := U₁) U₂)]
  [MeasurableSpace (QuotientSpace (U := U₀) U₂)] in
/-- Genuine absolute product convergence, tested against every original smooth
functional, at every ambient argument. It does not assert representability. -/
def OrderedScalarIntegrable
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A) : Prop :=
  ∀ g : G, HarmonicAnalysis.SmoothWeakIntegral.ScalarProductIntegrable
    A.representation μV μW
    (fun p => eval P₀ (leviInflatedInducingRepresentation h₀ hU₀ A) f
      (((p.1 : G) * (p.2 : G)) * g))

variable [SFinite μV] [SFinite μW]
  (h₁₀ : MeasurePreserving C.first μV ν₁₀)
  (h₂₁ : MeasurePreserving C.second μW ν₂₁)
  (h₂₀ : MeasurePreserving C.composite (μV.prod μW) ν₂₀)

include C h₁₀ h₂₁ h₂₀

/-- Ordered multiplication and scalar Fubini identify the actual direct
quotient integral with the composite. Both intermediate and final representatives
stay in the original carrier. No direct-domain hypothesis is used. -/
theorem HasIntegral.comp_ordered
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f) :
    HasIntegral h₀ hU₀ U₂ A ν₂₀ f J := by
  intro g
  apply (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_measurePreserving_equiv_iff
    C.composite h₂₀ _ _).mpr
  have hinner : ∀ᵐ (w : W) ∂μW,
      HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation μV
        (fun v : V => eval P₀ (leviInflatedInducingRepresentation h₀ hU₀ A) f
          (((v : G) * (w : G)) * g))
        (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F ((w : G) * g)) := by
    apply Filter.Eventually.of_forall
    intro w
    have hi := (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_measurePreserving_equiv_iff
      C.first h₁₀ _ _).mp (hf ((w : G) * g))
    simpa only [C.first_eq, integrand_mk, Subgroup.coe_inclusion, mul_assoc] using hi
  have houter : HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation μW
      (fun w : W => eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F
        ((w : G) * g)) (J g) := by
    have ho := (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_measurePreserving_equiv_iff
      C.second h₂₁ _ _).mp (hF g)
    simpa only [C.second_eq, integrand_mk, Subgroup.coe_inclusion] using ho
  have hp := houter.prod (ha g) hinner
  simpa only [C.composite_eq, integrand_mk, Subgroup.coe_mul, Subgroup.coe_inclusion]
    using hp

/-- Existence of the two actual integrals and product absolute convergence
prove membership in the direct convergence and representability domain. -/
theorem mem_domain_comp_ordered
    {f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A}
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f) :
    f ∈ domain h₀ hU₀ U₂ A ν₂₀ :=
  (mem_domain h₀ hU₀ U₂ A ν₂₀ f).mpr
    ⟨J, hf.comp_ordered h₀ hU₀ h₁ hU₁ A C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ hF ha⟩

/-- The selected direct standard integral equals the represented composite
function. This uses uniqueness only after establishing the integral relation. -/
theorem operator_eq_comp_ordered (hM : IsClosed (M : Set G))
    (f : domain h₀ hU₀ U₂ A ν₂₀)
    {F : (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A}
    {J : G → A}
    (hf : HasIntegral h₀ hU₀ U₁ A ν₁₀ f.val
      (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) F))
    (hF : HasIntegral h₁ hU₁ U₂ A ν₂₁ F J)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f.val) :
    operator h₀ hU₀ U₂ A ν₂₀ hM f = J :=
  operator_eq h₀ hU₀ U₂ A ν₂₀ hM f
    (hf.comp_ordered h₀ hU₀ h₁ hU₁ A C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ hF ha)

section FirstTarget

variable [T2Space G]
  [MeasurableSpace U₁] [BorelSpace U₁]
  [MeasurableSpace (U₀.subgroupOf U₁)] [BorelSpace (U₀.subgroupOf U₁)]
  [BorelSpace (QuotientSpace (U := U₀) U₁)]
  (μU₁ : Measure U₁) (μI₁₀ : Measure (U₀.subgroupOf U₁))
  [Measure.IsHaarMeasure μU₁] [μU₁.Regular] [Measure.IsMulRightInvariant μU₁]
  [Measure.IsHaarMeasure μI₁₀] [μI₁₀.Regular] [Measure.IsMulRightInvariant μI₁₀]
  (hν₁₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₁) μU₁ μI₁₀ ν₁₀)
  (hM : IsClosed (M : Set G))
  (hsq₁₀ : SquaredModulusCompatibility h₀ hU₀ h₁ hU₁)

/-- When the intermediate vector is the actual target-valued standard
integral, convergence of its outer integral proves direct-domain membership. -/
theorem targetOperator_mem_domain_comp_ordered
    (f : domain h₀ hU₀ U₁ A ν₁₀)
    (hF : targetOperator h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f ∈
      domain h₁ hU₁ U₂ A ν₂₁)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f.val) :
    f.val ∈ domain h₀ hU₀ U₂ A ν₂₀ :=
  mem_domain_comp_ordered h₀ hU₀ h₁ hU₁ A C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀
    (targetOperator_spec h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f)
    (operator_spec h₁ hU₁ U₂ A ν₂₁ hM ⟨_, hF⟩) ha

/-- Equality of the actual selected direct and iterated integrals as
functions on the ambient group, with direct-domain membership derived. -/
theorem operator_comp_targetOperator_ordered
    (f : domain h₀ hU₀ U₁ A ν₁₀)
    (hF : targetOperator h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f ∈
      domain h₁ hU₁ U₂ A ν₂₁)
    (ha : OrderedScalarIntegrable h₀ hU₀ A μV μW f.val) :
    operator h₀ hU₀ U₂ A ν₂₀ hM
        ⟨f.val, targetOperator_mem_domain_comp_ordered h₀ hU₀ h₁ hU₁ A
          C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f hF ha⟩ =
      operator h₁ hU₁ U₂ A ν₂₁ hM
        ⟨targetOperator h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f, hF⟩ :=
  operator_eq_comp_ordered h₀ hU₀ h₁ hU₁ A C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀
    hM _ (targetOperator_spec h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ f)
    (operator_spec h₁ hU₁ U₂ A ν₂₁ hM ⟨_, hF⟩) ha

include hν₁₀ hM hsq₁₀ in
/-- Full domains of the successive integrals and absolute product convergence
for every source vector imply the direct integral's full domain. -/
theorem domain_eq_top_comp_ordered
    (hfull₁₀ : domain h₀ hU₀ U₁ A ν₁₀ = ⊤)
    (hfull₂₁ : domain h₁ hU₁ U₂ A ν₂₁ = ⊤)
    (ha : ∀ f, OrderedScalarIntegrable h₀ hU₀ A μV μW f) :
    domain h₀ hU₀ U₂ A ν₂₀ = ⊤ := by
  apply top_unique
  intro f _
  exact targetOperator_mem_domain_comp_ordered h₀ hU₀ h₁ hU₁ A
    C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀
    (sourceToDomain h₀ hU₀ A ν₁₀ hfull₁₀ f)
    (by rw [hfull₂₁]; exact Submodule.mem_top) (ha f)

section FullTarget

variable {P₂ : Subgroup G}
  (h₂ : IsSemidirectDecomposition P₂ M U₂) (hU₂ : IsClosed (U₂ : Set G))
  [MeasurableSpace U₂] [BorelSpace U₂]
  [MeasurableSpace (U₁.subgroupOf U₂)] [BorelSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace (U₀.subgroupOf U₂)] [BorelSpace (U₀.subgroupOf U₂)]
  [BorelSpace (QuotientSpace (U := U₁) U₂)]
  [BorelSpace (QuotientSpace (U := U₀) U₂)]
  (μU₂ : Measure U₂)
  (μI₂₁ : Measure (U₁.subgroupOf U₂)) (μI₂₀ : Measure (U₀.subgroupOf U₂))
  [Measure.IsHaarMeasure μU₂] [μU₂.Regular] [Measure.IsMulRightInvariant μU₂]
  [Measure.IsHaarMeasure μI₂₁] [μI₂₁.Regular] [Measure.IsMulRightInvariant μI₂₁]
  [Measure.IsHaarMeasure μI₂₀] [μI₂₀.Regular] [Measure.IsMulRightInvariant μI₂₀]
  (hν₂₁ : QuotientIntegration.IsCompatible (U₁.subgroupOf U₂) μU₂ μI₂₁ ν₂₁)
  (hν₂₀ : QuotientIntegration.IsCompatible (U₀.subgroupOf U₂) μU₂ μI₂₀ ν₂₀)
  (hsq₂₁ : SquaredModulusCompatibility h₁ hU₁ h₂ hU₂)
  (hsq₂₀ : SquaredModulusCompatibility h₀ hU₀ h₂ hU₂)

/-- Composition of actual ambient intertwining maps on the whole source,
conditional on the displayed convergence, quotient charts and Haar/modulus
comparisons. The direct full domain is derived from those of the two legs. -/
theorem fullSourceIntertwiner_comp_ordered
    (hfull₁₀ : domain h₀ hU₀ U₁ A ν₁₀ = ⊤)
    (hfull₂₁ : domain h₁ hU₁ U₂ A ν₂₁ = ⊤)
    (ha : ∀ f, OrderedScalarIntegrable h₀ hU₀ A μV μW f) :
    let hfull₂₀ := domain_eq_top_comp_ordered h₀ hU₀ h₁ hU₁ A
      C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ hfull₁₀ hfull₂₁ ha
    fullSourceIntertwiner h₀ hU₀ h₂ hU₂ A ν₂₀ μU₂ μI₂₀ hν₂₀ hM hsq₂₀ hfull₂₀ =
      (fullSourceIntertwiner h₁ hU₁ h₂ hU₂ A ν₂₁ μU₂ μI₂₁ hν₂₁ hM hsq₂₁ hfull₂₁).comp
        (fullSourceIntertwiner h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ hfull₁₀) := by
  dsimp only
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  exact operator_eq_comp_ordered h₀ hU₀ h₁ hU₁ A C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀
    hM (sourceToDomain h₀ hU₀ A ν₂₀
      (domain_eq_top_comp_ordered h₀ hU₀ h₁ hU₁ A
        C μV μW ν₁₀ ν₂₁ ν₂₀ h₁₀ h₂₁ h₂₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ hfull₁₀ hfull₂₁ ha) f)
    (fullSourceIntertwiner_spec h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ hfull₁₀ f)
    (fullSourceIntertwiner_spec h₁ hU₁ h₂ hU₂ A ν₂₁ μU₂ μI₂₁ hν₂₁ hM hsq₂₁ hfull₂₁
      (fullSourceIntertwiner h₀ hU₀ h₁ hU₁ A ν₁₀ μU₁ μI₁₀ hν₁₀ hM hsq₁₀ hfull₁₀ f))
    (ha f)

end FullTarget

end FirstTarget

end Integral

end Langlands.Plancherel.StandardIntertwining
