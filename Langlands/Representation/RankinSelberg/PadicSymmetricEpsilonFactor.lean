import Langlands.Representation.RankinSelberg.PadicEqualRankEpsilonFactor
import Langlands.Representation.RankinSelberg.PadicUnequalRankEpsilonFactor

/-! Constructed generic p-adic epsilon factors for all positive rank pairs. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance padicSymmetricEpsilonNormedField : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance padicSymmetricEpsilonValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance padicSymmetricEpsilonLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance padicSymmetricEpsilonNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier := valuative_nonarchimedean
local instance padicSymmetricEpsilonMeasurableSpace : MeasurableSpace F.Carrier := borel F.Carrier
local instance padicSymmetricEpsilonBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Ordered

variable (hnr : n ≤ r)
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

include hnr hν hπ hσ in
/-- Actual epsilon existence, including equal and strictly unequal ranks. -/
theorem genericPairEpsilonFactorExists :
    ∃ e : ℂˣ × ℤ, IsPadicPairEpsilonFactor F ψ ν π σ e := by
  rcases lt_or_eq_of_le hnr with hlt | heq
  · exact ⟨genericUnequalRankEpsilonData F hlt ψ ν hν π σ hπ hσ,
      genericUnequalRankEpsilonData_isPadic F hlt ψ ν hν π σ hπ hσ⟩
  · subst r
    exact ⟨genericEqualRankEpsilonData F ψ ν hν π σ hπ hσ,
      genericEqualRankEpsilonData_isPadic F ψ ν hν π σ hπ hσ⟩

/-- The coefficient and exponent chosen from proved larger-first existence. -/
def genericPairEpsilonData : ℂˣ × ℤ :=
  (genericPairEpsilonFactorExists F hnr ψ ν hν π σ hπ hσ).choose

theorem genericPairEpsilonData_isPadic :
    IsPadicPairEpsilonFactor F ψ ν π σ
      (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ) :=
  (genericPairEpsilonFactorExists F hnr ψ ν hν π σ hπ hσ).choose_spec

theorem genericPairEpsilonData_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ = e :=
  (genericPairEpsilonData_isPadic F hnr ψ ν hν π σ hπ hσ).unique he

/-- The actual larger-first rational-function epsilon unit. -/
def genericPairEpsilonFactor : RationalFunctionsˣ :=
  rationalEpsilonMonomial (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).1
    (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).2

@[simp] theorem coe_genericPairEpsilonFactor :
    (genericPairEpsilonFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions
        ((genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).2 :=
  coe_rationalEpsilonMonomial _ _

theorem genericPairEpsilonFactor_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    genericPairEpsilonFactor F hnr ψ ν hν π σ hπ hσ =
      rationalEpsilonMonomial e.1 e.2 := by
  unfold genericPairEpsilonFactor
  rw [genericPairEpsilonData_eq F hnr ψ ν hν π σ hπ hσ he]

/-- The actual larger-first epsilon value as a complex unit at every parameter. -/
def genericPairEpsilonValue (s : ℂ) : ℂˣ :=
  Units.mk0
    (epsilonMonomial F.canonicalTopologicalData.residueCardinality
      (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).1
      (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).2 s)
    (epsilonMonomial_ne_zero _ (by
      exact_mod_cast (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one))
      _ _ s)

@[simp] theorem coe_genericPairEpsilonValue (s : ℂ) :
    (genericPairEpsilonValue F hnr ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).1
        (genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ).2 s := rfl

theorem genericPairEpsilonValue_eq {e : ℂˣ × ℤ}
    (he : IsPadicPairEpsilonFactor F ψ ν π σ e) (s : ℂ) :
    (genericPairEpsilonValue F hnr ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality e.1 e.2 s := by
  rw [coe_genericPairEpsilonValue, genericPairEpsilonData_eq F hnr ψ ν hν π σ hπ hσ he]

theorem genericPairEpsilonData_of_lt (hlt : n < r) :
    genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ =
      genericUnequalRankEpsilonData F hlt ψ ν hν π σ hπ hσ :=
  genericPairEpsilonData_eq F hnr ψ ν hν π σ hπ hσ
    (genericUnequalRankEpsilonData_isPadic F hlt ψ ν hν π σ hπ hσ)

theorem genericPairEpsilonData_self
    (π₀ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ₀ : Whittaker.IsGeneric ψ n π₀) :
    genericPairEpsilonData F (Nat.le_refl n) ψ ν hν π₀ σ hπ₀ hσ =
      genericEqualRankEpsilonData F ψ ν hν π₀ σ hπ₀ hσ :=
  genericPairEpsilonData_eq F (Nat.le_refl n) ψ ν hν π₀ σ hπ₀ hσ
    (genericEqualRankEpsilonData_isPadic F ψ ν hν π₀ σ hπ₀ hσ)

end Ordered

section Symmetric

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The actual epsilon data for either rank order, using the larger rank first. -/
def genericSymmetricEpsilonData : ℂˣ × ℤ :=
  if hnr : n ≤ r then
    genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ
  else
    genericPairEpsilonData F (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) ψ ν hν σ π hσ hπ

theorem genericSymmetricEpsilonData_of_le (hnr : n ≤ r) :
    genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ =
      genericPairEpsilonData F hnr ψ ν hν π σ hπ hσ := by
  simp only [genericSymmetricEpsilonData, dite_eq_left hnr]

theorem genericSymmetricEpsilonData_of_lt (hrn : r < n) :
    genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ =
      genericPairEpsilonData F hrn.le ψ ν hν σ π hσ hπ := by
  simp only [genericSymmetricEpsilonData, dite_eq_right (Nat.not_le.mpr hrn)]

/-- The full integral relation includes compatible-measure and functional witnesses. -/
theorem genericSymmetricEpsilonData_isPadic :
    IsPadicSymmetricEpsilonFactor F ψ ν π σ
      (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ) := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricEpsilonData_of_le F ψ ν hν π σ hπ hσ hnr]
    exact (isPadicSymmetricEpsilonFactor_of_le hnr).mpr
      (genericPairEpsilonData_isPadic F hnr ψ ν hν π σ hπ hσ)
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricEpsilonData_of_lt F ψ ν hν π σ hπ hσ hrn]
    exact (isPadicSymmetricEpsilonFactor_of_lt hrn).mpr
      (genericPairEpsilonData_isPadic F hrn.le ψ ν hν σ π hσ hπ)

theorem genericSymmetricEpsilonData_eq {e : ℂˣ × ℤ}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ = e :=
  (genericSymmetricEpsilonData_isPadic F ψ ν hν π σ hπ hσ).unique he

/-- The actual epsilon rational-function unit in either rank order. -/
def genericSymmetricEpsilonFactor : RationalFunctionsˣ :=
  rationalEpsilonMonomial (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1
    (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2

@[simp] theorem coe_genericSymmetricEpsilonFactor :
    (genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ : RationalFunctions) =
      algebraMap ℂ RationalFunctions
        ((genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1 : ℂ) *
        RatFunc.X ^ (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2 :=
  coe_rationalEpsilonMonomial _ _

theorem genericSymmetricEpsilonFactor_eq {e : ℂˣ × ℤ}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) :
    genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ =
      rationalEpsilonMonomial e.1 e.2 := by
  unfold genericSymmetricEpsilonFactor
  rw [genericSymmetricEpsilonData_eq F ψ ν hν π σ hπ hσ he]

/-- The everywhere nonzero epsilon value in either rank order. -/
def genericSymmetricEpsilonValue (s : ℂ) : ℂˣ :=
  Units.mk0
    (epsilonMonomial F.canonicalTopologicalData.residueCardinality
      (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1
      (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2 s)
    (epsilonMonomial_ne_zero _ (by
      exact_mod_cast (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one))
      _ _ s)

@[simp] theorem coe_genericSymmetricEpsilonValue (s : ℂ) :
    (genericSymmetricEpsilonValue F ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2 s := rfl

theorem genericSymmetricEpsilonValue_eq {e : ℂˣ × ℤ}
    (he : IsPadicSymmetricEpsilonFactor F ψ ν π σ e) (s : ℂ) :
    (genericSymmetricEpsilonValue F ψ ν hν π σ hπ hσ s : ℂ) =
      epsilonMonomial F.canonicalTopologicalData.residueCardinality e.1 e.2 s := by
  rw [coe_genericSymmetricEpsilonValue,
    genericSymmetricEpsilonData_eq F ψ ν hν π σ hπ hσ he]

theorem genericSymmetricEpsilonFactor_of_le (hnr : n ≤ r) :
    genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ =
      genericPairEpsilonFactor F hnr ψ ν hν π σ hπ hσ := by
  unfold genericSymmetricEpsilonFactor genericPairEpsilonFactor
  rw [genericSymmetricEpsilonData_of_le F ψ ν hν π σ hπ hσ hnr]

theorem genericSymmetricEpsilonFactor_of_lt (hrn : r < n) :
    genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ =
      genericPairEpsilonFactor F hrn.le ψ ν hν σ π hσ hπ := by
  unfold genericSymmetricEpsilonFactor genericPairEpsilonFactor
  rw [genericSymmetricEpsilonData_of_lt F ψ ν hν π σ hπ hσ hrn]

end Symmetric

end Langlands.RankinSelberg
