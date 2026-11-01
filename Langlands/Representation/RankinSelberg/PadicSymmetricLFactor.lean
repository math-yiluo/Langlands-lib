import Langlands.Representation.RankinSelberg.PadicPairLFactor

/-!
# Constructed generic p-adic L-factors in either rank order

Apply the existing larger-first construction in the rank order prescribed by
`IsPadicSymmetricLPolynomial`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : MeasurableSpace F.Carrier := borel F.Carrier

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The actual normalized L-polynomial, using the larger rank first. -/
def genericSymmetricLPolynomial : ℂ[X] :=
  if hnr : n ≤ r then
    genericPairLPolynomial F hnr ψ ν π σ hπ hσ
  else
    genericPairLPolynomial F (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) ψ ν σ π hσ hπ

/-- The actual rational-function L-unit in either rank order. -/
def genericSymmetricLFactor : RationalFunctionsˣ :=
  if hnr : n ≤ r then
    genericPairLFactor F hnr ψ ν π σ hπ hσ
  else
    genericPairLFactor F (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) ψ ν σ π hσ hπ

theorem genericSymmetricLPolynomial_of_le (hnr : n ≤ r) :
    genericSymmetricLPolynomial F ψ ν π σ hπ hσ =
      genericPairLPolynomial F hnr ψ ν π σ hπ hσ := by
  simp only [genericSymmetricLPolynomial, dite_eq_left hnr]

theorem genericSymmetricLPolynomial_of_lt (hrn : r < n) :
    genericSymmetricLPolynomial F ψ ν π σ hπ hσ =
      genericPairLPolynomial F hrn.le ψ ν σ π hσ hπ := by
  simp only [genericSymmetricLPolynomial, dite_eq_right (Nat.not_le.mpr hrn)]

theorem genericSymmetricLFactor_of_le (hnr : n ≤ r) :
    genericSymmetricLFactor F ψ ν π σ hπ hσ =
      genericPairLFactor F hnr ψ ν π σ hπ hσ := by
  simp only [genericSymmetricLFactor, dite_eq_left hnr]

theorem genericSymmetricLFactor_of_lt (hrn : r < n) :
    genericSymmetricLFactor F ψ ν π σ hπ hσ =
      genericPairLFactor F hrn.le ψ ν σ π hσ hπ := by
  simp only [genericSymmetricLFactor, dite_eq_right (Nat.not_le.mpr hrn)]

/-- This is the complete relation, including compatible-measure existence. -/
theorem genericSymmetricLPolynomial_isPadic :
    IsPadicSymmetricLPolynomial F ψ ν π σ
      (genericSymmetricLPolynomial F ψ ν π σ hπ hσ) := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact (isPadicSymmetricLPolynomial_of_le hnr).mpr
      (genericPairLPolynomial_isPadic F hnr ψ ν π σ hπ hσ)
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact (isPadicSymmetricLPolynomial_of_lt hrn).mpr
      (genericPairLPolynomial_isPadic F hrn.le ψ ν σ π hσ hπ)

@[simp] theorem genericSymmetricLPolynomial_coeff_zero :
    (genericSymmetricLPolynomial F ψ ν π σ hπ hσ).coeff 0 = 1 := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact genericPairLPolynomial_coeff_zero F hnr ψ ν π σ hπ hσ
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact genericPairLPolynomial_coeff_zero F hrn.le ψ ν σ π hσ hπ

theorem genericSymmetricLPolynomial_eq {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P) :
    genericSymmetricLPolynomial F ψ ν π σ hπ hσ = P :=
  (genericSymmetricLPolynomial_isPadic F ψ ν π σ hπ hσ).unique hP

@[simp] theorem coe_genericSymmetricLFactor :
    (genericSymmetricLFactor F ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions
        (genericSymmetricLPolynomial F ψ ν π σ hπ hσ))⁻¹ := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricLFactor_of_le F ψ ν π σ hπ hσ hnr,
      genericSymmetricLPolynomial_of_le F ψ ν π σ hπ hσ hnr]
    exact coe_genericPairLFactor F hnr ψ ν π σ hπ hσ
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricLFactor_of_lt F ψ ν π σ hπ hσ hrn,
      genericSymmetricLPolynomial_of_lt F ψ ν π σ hπ hσ hrn]
    exact coe_genericPairLFactor F hrn.le ψ ν σ π hσ hπ

theorem genericSymmetricLFactor_eq {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P) :
    (genericSymmetricLFactor F ψ ν π σ hπ hσ : RationalFunctions) =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  rw [coe_genericSymmetricLFactor,
    genericSymmetricLPolynomial_eq F ψ ν π σ hπ hσ hP]

end Langlands.RankinSelberg
