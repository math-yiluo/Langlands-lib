import Langlands.Representation.Plancherel.NestedStandardIntertwiningIntegral

/-! # The standard intertwining operator under Levi restriction -/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Induction

namespace Langlands.Plancherel.StandardIntertwining

universe u uV

section FullOperator

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ : Subgroup G}
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (A : SmoothRep.{0, u, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U₀) U₁)]

/-- A linear map between the actual normalized source and target models
represents the weak standard integral on the entire source. -/
def RepresentsStandardIntegral
    (ν : Measure (QuotientSpace (U := U₀) U₁))
    (J : ((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A) →ₗ[ℂ]
      ((DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A)) : Prop :=
  ∀ f, HasIntegral h₀ hU₀ U₁ A ν f
    (eval P₁ (leviInflatedInducingRepresentation h₁ hU₁ A) (J f))

end FullOperator

variable {G : Type u} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P₀ P₁ M U₀ U₁ Q L N : Subgroup G} [LocallyCompactSpace L]
  (h₀ : IsSemidirectDecomposition P₀ M U₀) (hU₀ : IsClosed (U₀ : Set G))
  (h₁ : IsSemidirectDecomposition P₁ M U₁) (hU₁ : IsClosed (U₁ : Set G))
  (h₀i : IsSemidirectDecomposition (P₀.subgroupOf L) (M.subgroupOf L) (U₀.subgroupOf L))
  (h₁i : IsSemidirectDecomposition (P₁.subgroupOf L) (M.subgroupOf L) (U₁.subgroupOf L))
  (hML : M ≤ L) (hQ : IsSemidirectDecomposition Q L N)
  (hU₁Q : U₁ ≤ Q) (hNU₀ : N ≤ U₀) (hNU₁ : N ≤ U₁) (hπ : Continuous hQ.projection)
  (A : SmoothRep.{0, u, uV} ℂ M)

set_option hygiene false in
local notation "hU₀i" => hU₀.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "hU₁i" => hU₁.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))
set_option hygiene false in
local notation "Ai" => SmoothRep.pullback (subgroupOfContinuousEquiv hML) A
set_option hygiene false in
set_option quotPrecheck false in
local notation "X₀" => ↥((DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj A)
set_option hygiene false in
set_option quotPrecheck false in
local notation "X₁" => ↥((DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj A)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Y₀" => ↥((DynamicNormalization.leviTwistedInductionFunctor h₀i hU₀i).obj Ai)
set_option hygiene false in
set_option quotPrecheck false in
local notation "Y₁" => ↥((DynamicNormalization.leviTwistedInductionFunctor h₁i hU₁i).obj Ai)

local instance operatorAmbientMeasurable : MeasurableSpace (QuotientSpace (U := U₀) U₁) := borel _
local instance operatorInnerMeasurable :
    MeasurableSpace (QuotientSpace (U := U₀.subgroupOf L) (U₁.subgroupOf L)) := borel _

variable (ν : Measure (QuotientSpace (U := U₀) U₁)) (c : L →* ℂˣ)
  (hc : ∀ u : U₁.subgroupOf L, c u.val = 1)
  (R₀ : X₀ →ₗ[ℂ] Y₀) (R₁ : X₁ →ₗ[ℂ] Y₁)
  (hR₀ : ∀ f, NestedRestrictionFormula h₀ hU₀ h₀i hML A c f 1 (R₀ f))
  (hR₁ : ∀ f, NestedRestrictionFormula h₁ hU₁ h₁i hML A c f 1 (R₁ f))
  (J : X₀ →ₗ[ℂ] X₁) (hJ : RepresentsStandardIntegral h₀ hU₀ h₁ hU₁ A ν J)

set_option hygiene false in
local notation "νi" => nestedQuotientMeasure hQ hU₁Q hNU₀ hNU₁ hπ ν

include hc hR₀ hR₁ hJ in
/-- The restriction of an ambient operator value represents the inner
weak standard integral on the restricted source vector. -/
theorem RepresentsStandardIntegral.nested_apply (f : X₀) :
    HasIntegral h₀i hU₀i (U₁.subgroupOf L) Ai νi (R₀ f)
      (eval (P₁.subgroupOf L) (leviInflatedInducingRepresentation h₁i hU₁i Ai) (R₁ (J f))) := by
  have h := (hJ f).nested_restriction h₀ hU₀ h₀i hML hQ hU₁Q hNU₀ hNU₁ hπ A ν c hc
    1 (R₀ f) (hR₀ f)
  have he := funext (hR₁ (J f))
  exact he ▸ h

include hc hR₀ hR₁ hJ in
/-- A fixed linear section of the source restriction constructs the inner
standard operator on its full source, with the exact pushed-forward scale. -/
theorem RepresentsStandardIntegral.nested_comp
    (S : Y₀ →ₗ[ℂ] X₀) (hS : R₀.comp S = LinearMap.id) :
    RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i Ai νi (R₁.comp (J.comp S)) := by
  intro f
  have h := RepresentsStandardIntegral.nested_apply h₀ hU₀ h₁ hU₁ h₀i h₁i
    hML hQ hU₁Q hNU₀ hNU₁ hπ A ν c hc R₀ R₁ hR₀ hR₁ J hJ (S f)
  have he : R₀ (S f) = f := LinearMap.congr_fun hS f
  exact (congrArg (fun y : Y₀ => HasIntegral h₀i hU₀i (U₁.subgroupOf L) Ai νi y
    (eval (P₁.subgroupOf L) (leviInflatedInducingRepresentation h₁i hU₁i Ai) (R₁ (J (S f))))) he).mp h

include hc hR₀ hR₁ hJ in
/-- Weak-integral uniqueness gives the exact operator square for any inner
operator representing the integral at the prescribed pushed-forward scale. -/
theorem RepresentsStandardIntegral.nested_square
    (hM : IsClosed (M : Set G))
    (Ji : Y₀ →ₗ[ℂ] Y₁) (hJi : RepresentsStandardIntegral h₀i hU₀i h₁i hU₁i Ai νi Ji) :
    Ji.comp R₀ = R₁.comp J := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext l
  have h := RepresentsStandardIntegral.nested_apply h₀ hU₀ h₁ hU₁ h₀i h₁i
    hML hQ hU₁Q hNU₀ hNU₁ hπ A ν c hc R₀ R₁ hR₀ hR₁ J hJ f
  change eval (P₁.subgroupOf L) (leviInflatedInducingRepresentation h₁i hU₁i Ai) (Ji (R₀ f)) l =
    eval (P₁.subgroupOf L) (leviInflatedInducingRepresentation h₁i hU₁i Ai) (R₁ (J f)) l
  exact (hJi (R₀ f) l).unique
    (compactCofinal (M := M.subgroupOf L)
      (hM.preimage (continuous_subtype_val : Continuous (Subtype.val : L → G))))
    (SmoothRep.pullback (subgroupOfContinuousEquiv hML) A).property (h l)

end Langlands.Plancherel.StandardIntertwining
