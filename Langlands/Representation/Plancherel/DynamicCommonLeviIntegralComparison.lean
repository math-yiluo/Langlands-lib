import Langlands.Representation.Plancherel.DynamicCommonLeviStructuralComparison

/-! # Weak standard integrals under the canonical literal subgroup comparisons -/

noncomputable section

set_option maxHeartbeats 400000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel.DynamicCommonLeviStructuralComparison

open Aubert.General Induction StandardIntertwining
open DynamicCommonLeviPresentationComparison

section Representation

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {M N : Subgroup H} (e : M = N) (A : SmoothRep.{0, u, uV} ℂ N)

/-- Admissibility survives the constructed identity on ambient Levi elements. -/
theorem representationOfEq_isAdmissible (hA : A.IsAdmissible) :
    (representationOfEq e A).IsAdmissible := by
  subst N
  exact hA

/-- The original carrier and action have the same finite composition length. -/
theorem representationOfEq_hasFiniteLength (hA : A.HasFiniteLength) :
    (representationOfEq e A).HasFiniteLength := by
  subst N
  exact hA

end Representation

section Integral

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P₀ M₀ U₀ V₀ P₁ M₁ U₁ V₁ : Subgroup H}
  (eP : P₀ = P₁) (eM : M₀ = M₁) (eU : U₀ = U₁) (eV : V₀ = V₁)
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (hU₀ : IsClosed (U₀ : Set H)) (hU₁ : IsClosed (U₁ : Set H))
  (A : SmoothRep.{0, u, uV} ℂ M₁)

local instance comparisonQuotientMeasurable (U V : Subgroup H) :
    MeasurableSpace (QuotientSpace (U := U) V) := borel _
local instance comparisonQuotientBorel (U V : Subgroup H) :
    BorelSpace (QuotientSpace (U := U) V) := ⟨rfl⟩

/-- The vector weak integrands agree on every ambient argument and quotient
point, through the actual quotient and induction comparisons. -/
theorem integrandComparisonOfEq (g : H)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM A)) (q : QuotientSpace (U := U₀) V₀) :
    integrand h₁ hU₁ V₁ A g
        (leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f)
        (quotientComparisonOfEq eU eV q) =
      integrand h₀ hU₀ V₀ (representationOfEq eM A) g f q := by
  subst P₁
  subst M₁
  subst U₁
  subst V₁
  rfl

/-- Exact pullback of the quotient measure transports both scalar absolute
integrability and its representing vector in the original carrier. -/
theorem hasIntegralComparisonOfEq
    (ν : Measure (QuotientSpace (U := U₁) V₁))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM A)) (Jf : H → A) :
    HasIntegral h₀ hU₀ V₀ (representationOfEq eM A)
        (quotientMeasureOfEq eU eV ν) f Jf ↔
      HasIntegral h₁ hU₁ V₁ A ν
        (leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f) Jf := by
  subst P₁
  subst M₁
  subst U₁
  subst V₁
  change HasIntegral h₀ hU₀ V₀ A (Measure.map id ν) f Jf ↔
    HasIntegral h₀ hU₀ V₀ A ν f Jf
  rw [Measure.map_id]

/-- The constructed induction map identifies the entire actual weak-integral
domain; no convergence assumption is used. -/
theorem memDomainComparisonOfEq
    (ν : Measure (QuotientSpace (U := U₁) V₁))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj
      (representationOfEq eM A)) :
    f ∈ domain h₀ hU₀ V₀ (representationOfEq eM A)
        (quotientMeasureOfEq eU eV ν) ↔
      leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f ∈
        domain h₁ hU₁ V₁ A ν := by
  rw [mem_domain, mem_domain]
  exact exists_congr (fun Jf =>
    hasIntegralComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν f Jf)

/-- The canonical linear identification of the entire weak-integral domains. -/
def domainComparisonOfEq
    (ν : Measure (QuotientSpace (U := U₁) V₁)) :
    domain h₀ hU₀ V₀ (representationOfEq eM A)
        (quotientMeasureOfEq eU eV ν) ≃ₗ[ℂ]
      domain h₁ hU₁ V₁ A ν := by
  let E := (leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁).toLinearEquiv
  refine E.ofSubmodules _ _ ?_
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (memDomainComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν f).mp hf
  · intro hg
    refine ⟨E.symm g, ?_, E.apply_symm_apply g⟩
    apply (memDomainComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν (E.symm g)).mpr
    change E (E.symm g) ∈ domain h₁ hU₁ V₁ A ν
    simpa only [E.apply_symm_apply] using hg

/-- The domain identification is the restriction of the constructed induction map. -/
theorem domainComparisonOfEq_coe
    (ν : Measure (QuotientSpace (U := U₁) V₁))
    (f : domain h₀ hU₀ V₀ (representationOfEq eM A)
      (quotientMeasureOfEq eU eV ν)) :
    (domainComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν f).val =
      leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f.val := by
  rfl

include eP in
/-- Full convergence transports in both directions with the fixed measure
scale and original inducing carrier. -/
theorem fullDomainComparisonOfEq
    (ν : Measure (QuotientSpace (U := U₁) V₁)) :
    domain h₀ hU₀ V₀ (representationOfEq eM A)
        (quotientMeasureOfEq eU eV ν) = ⊤ ↔
      domain h₁ hU₁ V₁ A ν = ⊤ := by
  subst P₁
  subst M₁
  subst U₁
  subst V₁
  change domain h₀ hU₀ V₀ A (Measure.map id ν) = ⊤ ↔
    domain h₀ hU₀ V₀ A ν = ⊤
  rw [Measure.map_id]

/-- The selected represented integral agrees at every ambient group argument. -/
theorem operatorComparisonOfEq
    (ν : Measure (QuotientSpace (U := U₁) V₁))
    (hM₀ : IsClosed (M₀ : Set H)) (hM₁ : IsClosed (M₁ : Set H))
    (f : domain h₀ hU₀ V₀ (representationOfEq eM A)
      (quotientMeasureOfEq eU eV ν)) (g : H) :
    operator h₁ hU₁ V₁ A ν hM₁
        ⟨leviInductionComparisonOfEq eP eM eU h₀ h₁ A hU₀ hU₁ f.val,
          (memDomainComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν f.val).mp f.property⟩ g =
      operator h₀ hU₀ V₀ (representationOfEq eM A)
        (quotientMeasureOfEq eU eV ν) hM₀ f g := by
  have hf := (hasIntegralComparisonOfEq eP eM eU eV h₀ h₁ hU₀ hU₁ A ν
    f.val _).mp (operator_spec h₀ hU₀ V₀ _ _ hM₀ f)
  exact congrFun (operator_eq h₁ hU₁ V₁ A ν hM₁ _ hf) g

end Integral

section SquaredModulus

attribute [local instance] equalitySubgroupMeasurable equalitySubgroupBorel
  equalityIntersectionMeasurable equalityIntersectionBorel
  equalityQuotientMeasurable equalityQuotientBorel

variable {H : Type u} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  [LocallyCompactSpace H]
  {P₀ P'₀ M₀ U₀ U'₀ P₁ P'₁ M₁ U₁ U'₁ : Subgroup H}
  (eP : P₀ = P₁) (eP' : P'₀ = P'₁) (eM : M₀ = M₁)
  (eU : U₀ = U₁) (eU' : U'₀ = U'₁)
  (h₀ : IsSemidirectDecomposition P₀ M₀ U₀)
  (h'₀ : IsSemidirectDecomposition P'₀ M₀ U'₀)
  (h₁ : IsSemidirectDecomposition P₁ M₁ U₁)
  (h'₁ : IsSemidirectDecomposition P'₁ M₁ U'₁)
  (hU₀ : IsClosed (U₀ : Set H)) (hU'₀ : IsClosed (U'₀ : Set H))
  (hU₁ : IsClosed (U₁ : Set H)) (hU'₁ : IsClosed (U'₁ : Set H))

include eP eP' eM eU eU' in
/-- The source squared-modulus conclusion is the actual dynamic conclusion
under the identity ambient subgroup maps. -/
theorem squaredModulusComparisonOfEq
    (hsq : SquaredModulusCompatibility h₀ hU₀ h'₀ hU'₀) :
    SquaredModulusCompatibility h₁ hU₁ h'₁ hU'₁ := by
  subst P₁
  subst P'₁
  subst M₁
  subst U₁
  subst U'₁
  exact hsq

end SquaredModulus

end Langlands.Plancherel.DynamicCommonLeviStructuralComparison
