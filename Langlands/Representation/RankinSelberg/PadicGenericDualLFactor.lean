import Langlands.Representation.RankinSelberg.PadicPairLFactor
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType

/-! Construct the actual inverse-transpose pair L-factors from genericity. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance padicGenericDualLNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance padicGenericDualLValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance padicGenericDualLLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance padicGenericDualLMeasurableSpace : MeasurableSpace F.Carrier :=
  borel F.Carrier

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- The supplied-topology construction has the full canonical intrinsic
specification for every pair of full Whittaker type. -/
theorem padicPairLPolynomial_isPadic (hnr : n ≤ r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ) :
    IsPadicPairLPolynomial F ψ ν π σ
      (padicPairLPolynomial F F.canonicalTopologicalData hnr ψ ν π σ hπ hσ) := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  constructor
  · exact ⟨inferInstance, unipotent_compatibleMeasureExists F.Carrier n⟩
  · intro _ μ hμ
    exact padicPairLPolynomial_spec F F.canonicalTopologicalData hnr ψ ν π σ hπ hσ μ hμ

variable (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

section Ordered

variable (hnr : n ≤ r)

/-- The normalized L-polynomial of the actual inverse-transpose pair for the
inverse additive character and the unchanged additive measure. -/
def genericPairDualLPolynomial : ℂ[X] :=
  padicPairLPolynomial F F.canonicalTopologicalData hnr (ψ.scale (-1)) ν
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π (isOfWhittakerType_of_isGeneric F hπ))
    (isOfWhittakerType_secondDual ψ σ (isOfInverseWhittakerType_of_isGeneric F hσ))

/-- The corresponding actual rational-function L-unit. -/
def genericPairDualLFactor : RationalFunctionsˣ :=
  padicPairLFactor F F.canonicalTopologicalData hnr (ψ.scale (-1)) ν
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π (isOfWhittakerType_of_isGeneric F hπ))
    (isOfWhittakerType_secondDual ψ σ (isOfInverseWhittakerType_of_isGeneric F hσ))

theorem genericPairDualLPolynomial_isPadic :
    IsPadicPairLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr) :=
  padicPairLPolynomial_isPadic F (ψ.scale (-1)) ν
    (inverseTransposePullback π) (inverseTransposePullback σ) hnr
    (isOfWhittakerType_firstDual ψ π (isOfWhittakerType_of_isGeneric F hπ))
    (isOfWhittakerType_secondDual ψ σ (isOfInverseWhittakerType_of_isGeneric F hσ))

@[simp] theorem genericPairDualLPolynomial_coeff_zero :
    (genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr).coeff 0 = 1 :=
  padicPairLPolynomial_coeff_zero F F.canonicalTopologicalData hnr (ψ.scale (-1)) ν
    (inverseTransposePullback π) (inverseTransposePullback σ)
    (isOfWhittakerType_firstDual ψ π (isOfWhittakerType_of_isGeneric F hπ))
    (isOfWhittakerType_secondDual ψ σ (isOfInverseWhittakerType_of_isGeneric F hσ))

theorem genericPairDualLPolynomial_eq {P : ℂ[X]}
    (hP : IsPadicPairLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P) :
    genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr = P :=
  (genericPairDualLPolynomial_isPadic F ψ ν π σ hπ hσ hnr).unique hP

@[simp] theorem coe_genericPairDualLFactor :
    (genericPairDualLFactor F ψ ν π σ hπ hσ hnr : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions
        (genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr))⁻¹ := rfl

theorem genericPairDualLFactor_eq {P : ℂ[X]}
    (hP : IsPadicPairLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P) :
    (genericPairDualLFactor F ψ ν π σ hπ hσ hnr : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_genericPairDualLFactor, genericPairDualLPolynomial_eq F ψ ν π σ hπ hσ hnr hP]

end Ordered

/-- The normalized inverse-transpose L-polynomial in either rank order. -/
def genericSymmetricDualLPolynomial : ℂ[X] :=
  if hnr : n ≤ r then
    genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr
  else
    genericPairDualLPolynomial F ψ ν σ π hσ hπ (Nat.le_of_lt (Nat.lt_of_not_ge hnr))

/-- The actual inverse-transpose L-unit in either rank order. -/
def genericSymmetricDualLFactor : RationalFunctionsˣ :=
  if hnr : n ≤ r then
    genericPairDualLFactor F ψ ν π σ hπ hσ hnr
  else
    genericPairDualLFactor F ψ ν σ π hσ hπ (Nat.le_of_lt (Nat.lt_of_not_ge hnr))

theorem genericSymmetricDualLPolynomial_of_le (hnr : n ≤ r) :
    genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ =
      genericPairDualLPolynomial F ψ ν π σ hπ hσ hnr := by
  simp only [genericSymmetricDualLPolynomial, dite_eq_left hnr]

theorem genericSymmetricDualLPolynomial_of_lt (hrn : r < n) :
    genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ =
      genericPairDualLPolynomial F ψ ν σ π hσ hπ hrn.le := by
  simp only [genericSymmetricDualLPolynomial, dite_eq_right (Nat.not_le.mpr hrn)]

theorem genericSymmetricDualLFactor_of_le (hnr : n ≤ r) :
    genericSymmetricDualLFactor F ψ ν π σ hπ hσ =
      genericPairDualLFactor F ψ ν π σ hπ hσ hnr := by
  simp only [genericSymmetricDualLFactor, dite_eq_left hnr]

theorem genericSymmetricDualLFactor_of_lt (hrn : r < n) :
    genericSymmetricDualLFactor F ψ ν π σ hπ hσ =
      genericPairDualLFactor F ψ ν σ π hσ hπ hrn.le := by
  simp only [genericSymmetricDualLFactor, dite_eq_right (Nat.not_le.mpr hrn)]

/-- The full intrinsic specification holds at every compatible quotient
measure and every valid unequal-rank block. -/
theorem genericSymmetricDualLPolynomial_isPadic :
    IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ) := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricDualLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact (isPadicSymmetricLPolynomial_of_le hnr).mpr
      (genericPairDualLPolynomial_isPadic F ψ ν π σ hπ hσ hnr)
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricDualLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact (isPadicSymmetricLPolynomial_of_lt hrn).mpr
      (genericPairDualLPolynomial_isPadic F ψ ν σ π hσ hπ hrn.le)

@[simp] theorem genericSymmetricDualLPolynomial_coeff_zero :
    (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ).coeff 0 = 1 := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricDualLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact genericPairDualLPolynomial_coeff_zero F ψ ν π σ hπ hσ hnr
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricDualLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact genericPairDualLPolynomial_coeff_zero F ψ ν σ π hσ hπ hrn.le

theorem genericSymmetricDualLPolynomial_eq {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P) :
    genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ = P :=
  (genericSymmetricDualLPolynomial_isPadic F ψ ν π σ hπ hσ).unique hP

@[simp] theorem coe_genericSymmetricDualLFactor :
    (genericSymmetricDualLFactor F ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions
        (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ))⁻¹ := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricDualLFactor_of_le F ψ ν π σ hπ hσ hnr,
      genericSymmetricDualLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact coe_genericPairDualLFactor F ψ ν π σ hπ hσ hnr
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricDualLFactor_of_lt F ψ ν π σ hπ hσ hrn,
      genericSymmetricDualLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact coe_genericPairDualLFactor F ψ ν σ π hσ hπ hrn.le

theorem genericSymmetricDualLFactor_eq {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) P) :
    (genericSymmetricDualLFactor F ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_genericSymmetricDualLFactor,
    genericSymmetricDualLPolynomial_eq F ψ ν π σ hπ hσ hP]

end Langlands.RankinSelberg
