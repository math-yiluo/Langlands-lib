import Langlands.Representation.RankinSelberg.PadicGenericGammaExpression
import Langlands.Correspondence.RankOneArithmeticEpsilonData

/-!
# Generic p-adic pair factors at the actual self-dual Haar measure

The published generic constructors take an additive Haar measure `ν` and a proof that it
is self-dual for `ψ`. The self-dual measure is unique, and the Library constructs it as
`Correspondence.localSelfDualHaar F ψ`. This file evaluates the generic epsilon, L, dual L
and gamma factors there, so they depend only on `ψ` and the pair, and proves that they
agree with the published constructors and satisfy their full relations at every self-dual
measure.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker Polynomial LocalFactor

universe uF uV uW uV₂ uW₂

private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance selfDualGenericNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance selfDualGenericValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance selfDualGenericLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance selfDualGenericNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier :=
  valuative_nonarchimedean
local instance selfDualGenericMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance selfDualGenericBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

variable {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W₂}

/-! ### Epsilon factors -/

/-- `ε(s, π × σ, ψ)`, as a unit of rational functions in `X = q^(-s)`, computed with the
actual self-dual Haar measure of `ψ` and the larger rank first. -/
def selfDualGenericEpsilonFactor : RationalFunctionsˣ :=
  genericSymmetricEpsilonFactor F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ

/-- Agreement with the published constructor at every self-dual Haar measure. -/
theorem selfDualGenericEpsilonFactor_eq_genericSymmetricEpsilonFactor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    selfDualGenericEpsilonFactor F ψ π σ hπ hσ =
      genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

/-- Every certified epsilon factor at a self-dual measure gives the constructed unit. -/
theorem selfDualGenericEpsilonFactor_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {e : ℂˣ × ℤ} (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    selfDualGenericEpsilonFactor F ψ π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 := by
  rw [selfDualGenericEpsilonFactor_eq_genericSymmetricEpsilonFactor F ψ π σ hπ hσ ν hν]
  exact genericSymmetricEpsilonFactor_eq F ψ ν hν π σ hπ hσ he

/-- At every self-dual measure the constructed unit is `c X^m` for a certified `(c, m)`. -/
theorem exists_isPadicSymmetricEpsilonFactor_selfDualGenericEpsilonFactor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    ∃ e : ℂˣ × ℤ, IsPadicSymmetricEpsilonFactor F ψ ν π σ e ∧
      selfDualGenericEpsilonFactor F ψ π σ hπ hσ = rationalEpsilonMonomial e.1 e.2 :=
  ⟨genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ,
    genericSymmetricEpsilonData_isPadic F ψ ν hν π σ hπ hσ,
    selfDualGenericEpsilonFactor_eq F ψ π σ hπ hσ ν hν
      (genericSymmetricEpsilonData_isPadic F ψ ν hν π σ hπ hσ)⟩

/-- `ε(s, π × σ, ψ)` as an everywhere nonzero complex number. -/
def selfDualGenericEpsilonValue (s : ℂ) : ℂˣ :=
  genericSymmetricEpsilonValue F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ s

theorem selfDualGenericEpsilonValue_eq_genericSymmetricEpsilonValue
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) (s : ℂ) :
    selfDualGenericEpsilonValue F ψ π σ hπ hσ s =
      genericSymmetricEpsilonValue F ψ ν hν π σ hπ hσ s := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

/-- The value is `c q^(-ms)` for every certified `(c, m)` at a self-dual measure. -/
theorem selfDualGenericEpsilonValue_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {e : ℂˣ × ℤ} (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e)
    (s : ℂ) :
    (selfDualGenericEpsilonValue F ψ π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality e.1 e.2 s := by
  rw [selfDualGenericEpsilonValue_eq_genericSymmetricEpsilonValue F ψ π σ hπ hσ ν hν]
  exact genericSymmetricEpsilonValue_eq F ψ ν hν π σ hπ hσ he s

/-- The epsilon factor depends only on the equivalence classes of `π` and `σ`. -/
theorem selfDualGenericEpsilonFactor_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    selfDualGenericEpsilonFactor F ψ π σ hπ hσ =
      selfDualGenericEpsilonFactor F ψ π₂ σ₂ hπ₂ hσ₂ := by
  rw [selfDualGenericEpsilonFactor_eq F ψ π σ hπ hσ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    ((IsPadicSymmetricEpsilonFactor.congr_equiv φ φ').mpr
      (genericSymmetricEpsilonData_isPadic F ψ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ) π₂ σ₂ hπ₂ hσ₂))]
  rfl

theorem selfDualGenericEpsilonValue_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) (s : ℂ) :
    selfDualGenericEpsilonValue F ψ π σ hπ hσ s =
      selfDualGenericEpsilonValue F ψ π₂ σ₂ hπ₂ hσ₂ s := by
  apply Units.ext
  rw [selfDualGenericEpsilonValue_eq F ψ π σ hπ hσ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    ((IsPadicSymmetricEpsilonFactor.congr_equiv φ φ').mpr
      (genericSymmetricEpsilonData_isPadic F ψ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ) π₂ σ₂ hπ₂ hσ₂))]
  rfl

/-! ### L-factors -/

/-- The normalized L-polynomial `P` with `L(s, π × σ) = P(q^(-s))⁻¹`, computed with the
actual self-dual Haar measure of `ψ` and the larger rank first. -/
def selfDualGenericLPolynomial : ℂ[X] :=
  genericSymmetricLPolynomial F ψ (Correspondence.localSelfDualHaar F ψ) π σ hπ hσ

/-- `L(s, π × σ)` as a unit of rational functions in `X = q^(-s)`. -/
def selfDualGenericLFactor : RationalFunctionsˣ :=
  genericSymmetricLFactor F ψ (Correspondence.localSelfDualHaar F ψ) π σ hπ hσ

theorem selfDualGenericLPolynomial_eq_genericSymmetricLPolynomial
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    selfDualGenericLPolynomial F ψ π σ hπ hσ =
      genericSymmetricLPolynomial F ψ ν π σ hπ hσ := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

theorem selfDualGenericLFactor_eq_genericSymmetricLFactor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    selfDualGenericLFactor F ψ π σ hπ hσ = genericSymmetricLFactor F ψ ν π σ hπ hσ := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

/-- The full L-polynomial relation at every self-dual Haar measure. -/
theorem selfDualGenericLPolynomial_isPadic (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) :
    IsPadicSymmetricLPolynomial F ψ ν π σ (selfDualGenericLPolynomial F ψ π σ hπ hσ) := by
  rw [selfDualGenericLPolynomial_eq_genericSymmetricLPolynomial F ψ π σ hπ hσ ν hν]
  exact genericSymmetricLPolynomial_isPadic F ψ ν π σ hπ hσ

theorem selfDualGenericLPolynomial_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P) :
    selfDualGenericLPolynomial F ψ π σ hπ hσ = P :=
  (selfDualGenericLPolynomial_isPadic F ψ π σ hπ hσ ν hν).unique hP

@[simp] theorem selfDualGenericLPolynomial_coeff_zero :
    (selfDualGenericLPolynomial F ψ π σ hπ hσ).coeff 0 = 1 :=
  genericSymmetricLPolynomial_coeff_zero F ψ _ π σ hπ hσ

@[simp] theorem coe_selfDualGenericLFactor :
    (selfDualGenericLFactor F ψ π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions (selfDualGenericLPolynomial F ψ π σ hπ hσ))⁻¹ :=
  coe_genericSymmetricLFactor F ψ _ π σ hπ hσ

theorem selfDualGenericLPolynomial_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    selfDualGenericLPolynomial F ψ π σ hπ hσ =
      selfDualGenericLPolynomial F ψ π₂ σ₂ hπ₂ hσ₂ :=
  selfDualGenericLPolynomial_eq F ψ π σ hπ hσ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    ((IsPadicSymmetricLPolynomial.congr_equiv φ φ').mpr
      (selfDualGenericLPolynomial_isPadic F ψ π₂ σ₂ hπ₂ hσ₂ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ)))

theorem selfDualGenericLFactor_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    selfDualGenericLFactor F ψ π σ hπ hσ = selfDualGenericLFactor F ψ π₂ σ₂ hπ₂ hσ₂ := by
  apply Units.ext
  rw [coe_selfDualGenericLFactor, coe_selfDualGenericLFactor,
    selfDualGenericLPolynomial_congr_equiv F ψ π σ hπ hσ φ φ' hπ₂ hσ₂]

/-! ### Dual L-factors -/

/-- The normalized L-polynomial of the contragredient pair, realized as the
inverse-transpose pair for `ψ⁻¹ = ψ.scale (-1)`, with the same self-dual measure. -/
def selfDualGenericDualLPolynomial : ℂ[X] :=
  genericSymmetricDualLPolynomial F ψ (Correspondence.localSelfDualHaar F ψ) π σ hπ hσ

/-- The L-factor of the inverse-transpose pair, as a unit of rational functions in
`X = q^(-s)`. -/
def selfDualGenericDualLFactor : RationalFunctionsˣ :=
  genericSymmetricDualLFactor F ψ (Correspondence.localSelfDualHaar F ψ) π σ hπ hσ

theorem selfDualGenericDualLPolynomial_eq_genericSymmetricDualLPolynomial
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    selfDualGenericDualLPolynomial F ψ π σ hπ hσ =
      genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

/-- The full inverse-transpose L-polynomial relation at every self-dual Haar measure. -/
theorem selfDualGenericDualLPolynomial_isPadic (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) :
    IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (selfDualGenericDualLPolynomial F ψ π σ hπ hσ) := by
  rw [selfDualGenericDualLPolynomial_eq_genericSymmetricDualLPolynomial F ψ π σ hπ hσ ν hν]
  exact genericSymmetricDualLPolynomial_isPadic F ψ ν π σ hπ hσ

theorem selfDualGenericDualLPolynomial_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P) :
    selfDualGenericDualLPolynomial F ψ π σ hπ hσ = P :=
  (selfDualGenericDualLPolynomial_isPadic F ψ π σ hπ hσ ν hν).unique hP

@[simp] theorem selfDualGenericDualLPolynomial_coeff_zero :
    (selfDualGenericDualLPolynomial F ψ π σ hπ hσ).coeff 0 = 1 :=
  genericSymmetricDualLPolynomial_coeff_zero F ψ _ π σ hπ hσ

@[simp] theorem coe_selfDualGenericDualLFactor :
    (selfDualGenericDualLFactor F ψ π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions
        (selfDualGenericDualLPolynomial F ψ π σ hπ hσ))⁻¹ :=
  coe_genericSymmetricDualLFactor F ψ _ π σ hπ hσ

/-! ### Gamma factors -/

/-- `γ(s, π × σ, ψ)`, as a unit of rational functions in `X = q^(-s)`, computed with the
actual self-dual Haar measure of `ψ` and the larger rank first. -/
def selfDualGenericGammaFactor : RationalFunctionsˣ :=
  genericSymmetricGammaFactor F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ

theorem selfDualGenericGammaFactor_eq_genericSymmetricGammaFactor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) :
    selfDualGenericGammaFactor F ψ π σ hπ hσ =
      genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ := by
  obtain rfl := Correspondence.eq_localSelfDualHaar F ψ ν hν
  rfl

/-- The full gamma relation at every self-dual Haar measure. -/
theorem selfDualGenericGammaFactor_isPadic (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) :
    IsPadicSymmetricGammaFactor F ψ ν π σ
      (selfDualGenericGammaFactor F ψ π σ hπ hσ : RationalFunctions) := by
  rw [selfDualGenericGammaFactor_eq_genericSymmetricGammaFactor F ψ π σ hπ hσ ν hν]
  exact genericSymmetricGammaFactor_isPadic F ψ ν hν π σ hπ hσ

theorem selfDualGenericGammaFactor_eq (ν : AdditiveHaarMeasure F.Carrier)
    (hν : IsSelfDual ψ ν) {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν π σ G) :
    (selfDualGenericGammaFactor F ψ π σ hπ hσ : RationalFunctions) = G :=
  (selfDualGenericGammaFactor_isPadic F ψ π σ hπ hσ ν hν).unique hG

theorem isPadicSymmetricGammaFactor_iff_eq_selfDualGenericGammaFactor
    (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν) {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔
      G = (selfDualGenericGammaFactor F ψ π σ hπ hσ : RationalFunctions) := by
  constructor
  · intro hG
    exact (selfDualGenericGammaFactor_eq F ψ π σ hπ hσ ν hν hG).symm
  · rintro rfl
    exact selfDualGenericGammaFactor_isPadic F ψ π σ hπ hσ ν hν

/-- `γ(s) = ε(s) L^∨(1 - s) / L(s)`, where `L^∨` is the L-factor of the inverse-transpose
pair; the reflection `X ↦ q⁻¹ X⁻¹` takes `q^(-s)` to `q^(-(1-s))`. -/
theorem selfDualGenericGammaFactor_eq_mul :
    selfDualGenericGammaFactor F ψ π σ hπ hσ =
      selfDualGenericEpsilonFactor F ψ π σ hπ hσ *
        Units.map (RationalReflection.subst (LocalFactor.residueReflection F)).toMonoidHom
          (selfDualGenericDualLFactor F ψ π σ hπ hσ) /
        selfDualGenericLFactor F ψ π σ hπ hσ :=
  genericSymmetricGammaFactor_eq_unit F ψ _ _ π σ hπ hσ

theorem selfDualGenericGammaFactor_congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂)
    (hπ₂ : Whittaker.IsGeneric ψ r π₂) (hσ₂ : Whittaker.IsGeneric ψ n σ₂) :
    selfDualGenericGammaFactor F ψ π σ hπ hσ =
      selfDualGenericGammaFactor F ψ π₂ σ₂ hπ₂ hσ₂ := by
  apply Units.ext
  exact selfDualGenericGammaFactor_eq F ψ π σ hπ hσ _
    (Correspondence.isSelfDual_localSelfDualHaar F ψ)
    ((IsPadicSymmetricGammaFactor.congr_equiv φ φ').mpr
      (selfDualGenericGammaFactor_isPadic F ψ π₂ σ₂ hπ₂ hσ₂ _
        (Correspondence.isSelfDual_localSelfDualHaar F ψ)))

/-- The parameters `s` at which the reduced denominator of the gamma factor does not vanish
at `q^(-s)`. -/
def selfDualGenericGammaRegularDomain : Set ℂ :=
  genericSymmetricGammaRegularDomain F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ

/-- `γ(s, π × σ, ψ)` as a complex number on the regular domain. -/
def selfDualGenericGammaValue (s : selfDualGenericGammaRegularDomain F ψ π σ hπ hσ) : ℂ :=
  genericSymmetricGammaValue F ψ (Correspondence.localSelfDualHaar F ψ)
    (Correspondence.isSelfDual_localSelfDualHaar F ψ) π σ hπ hσ s

theorem selfDualGenericGammaValue_eq (s : selfDualGenericGammaRegularDomain F ψ π σ hπ hσ) :
    selfDualGenericGammaValue F ψ π σ hπ hσ s =
      (selfDualGenericGammaFactor F ψ π σ hπ hσ : RationalFunctions).eval (RingHom.id ℂ)
        (spectralPoint F.canonicalTopologicalData.residueCardinality s.val) :=
  rfl

/-- Nonvanishing of the dual polynomial at `q^(-(1-s))` puts `s` in the regular domain. -/
theorem mem_selfDualGenericGammaRegularDomain_of_dualPolynomial (s : ℂ)
    (hPd : (selfDualGenericDualLPolynomial F ψ π σ hπ hσ).eval
      (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) ≠ 0) :
    s ∈ selfDualGenericGammaRegularDomain F ψ π σ hπ hσ :=
  mem_genericSymmetricGammaRegularDomain_of_dualPolynomial F ψ _ _ π σ hπ hσ s hPd

/-- Where the dual polynomial does not vanish at `q^(-(1-s))`,
`γ(s) = ε(s) P(q^(-s)) / P^∨(q^(-(1-s)))`. -/
theorem selfDualGenericGammaValue_eq_localFactors (s : ℂ)
    (hPd : (selfDualGenericDualLPolynomial F ψ π σ hπ hσ).eval
      (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) ≠ 0) :
    selfDualGenericGammaValue F ψ π σ hπ hσ
      ⟨s, mem_selfDualGenericGammaRegularDomain_of_dualPolynomial F ψ π σ hπ hσ s hPd⟩ =
      (selfDualGenericEpsilonValue F ψ π σ hπ hσ s : ℂ) *
        (selfDualGenericLPolynomial F ψ π σ hπ hσ).eval
          (spectralPoint F.canonicalTopologicalData.residueCardinality s) /
        (selfDualGenericDualLPolynomial F ψ π σ hπ hσ).eval
          (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) :=
  genericSymmetricGammaValue_eq_localFactors F ψ _ _ π σ hπ hσ s hPd

end Langlands.RankinSelberg
