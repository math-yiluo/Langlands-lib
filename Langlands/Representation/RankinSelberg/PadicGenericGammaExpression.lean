import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.PadicSymmetricEpsilonFactor
import Langlands.Representation.RankinSelberg.PadicSymmetricLFactor
import Langlands.Representation.RankinSelberg.PadicGenericDualLFactor
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof

/-! Assemble the actual generic gamma unit from the actual epsilon and L units. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker Polynomial LocalFactor

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

local instance padicGenericGammaExpressionNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance padicGenericGammaExpressionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance padicGenericGammaExpressionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance padicGenericGammaExpressionNonarchimedeanAddGroup :
    NonarchimedeanAddGroup F.Carrier := valuative_nonarchimedean
local instance padicGenericGammaExpressionMeasurableSpace : MeasurableSpace F.Carrier :=
  borel F.Carrier
local instance padicGenericGammaExpressionBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

variable {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

/-- The explicit gamma unit assembled from the actual generic epsilon and
original/dual L units, with the common larger-rank-first convention. -/
def genericSymmetricGammaUnit : RationalFunctionsˣ :=
  genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ *
    Units.map (RationalReflection.subst (LocalFactor.residueReflection F)).toMonoidHom
      (genericSymmetricDualLFactor F ψ ν π σ hπ hσ) /
    genericSymmetricLFactor F ψ ν π σ hπ hσ

/-- The assembly is exactly epsilon times the original polynomial divided by
the dual polynomial at the reflected variable. -/
theorem genericSymmetricGammaUnit_eq_expression :
    (genericSymmetricGammaUnit F ψ ν hν π σ hπ hσ : RationalFunctions) =
      rationalGammaExpression (LocalFactor.residueReflection F)
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2
        (genericSymmetricLPolynomial F ψ ν π σ hπ hσ)
        (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ) := by
  simp only [genericSymmetricGammaUnit, Units.val_div_eq_div_val, Units.val_mul,
    Units.coe_map]
  change (genericSymmetricEpsilonFactor F ψ ν hν π σ hπ hσ : RationalFunctions) *
    RationalReflection.subst (LocalFactor.residueReflection F)
      (genericSymmetricDualLFactor F ψ ν π σ hπ hσ : RationalFunctions) /
    (genericSymmetricLFactor F ψ ν π σ hπ hσ : RationalFunctions) = _
  rw [coe_genericSymmetricDualLFactor, coe_genericSymmetricLFactor, map_inv₀,
    RationalReflection.subst_polynomial]
  unfold rationalGammaExpression genericSymmetricEpsilonFactor
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The explicit assembly satisfies the full intrinsic gamma relation. -/
theorem genericSymmetricGammaUnit_isPadic :
    IsPadicSymmetricGammaFactor F ψ ν π σ
      (genericSymmetricGammaUnit F ψ ν hν π σ hπ hσ : RationalFunctions) := by
  apply (symmetricGammaExpression.{uF,uV,uW} p F ψ ⟨ν, hν⟩ r n π σ
    (genericSymmetricGammaConstructionInput F ψ ν hν π σ hπ hσ)
    (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ)
    (genericSymmetricLPolynomial F ψ ν π σ hπ hσ)
    (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ)
    (genericSymmetricEpsilonData_isPadic F ψ ν hν π σ hπ hσ)
    (genericSymmetricLPolynomial_isPadic F ψ ν π σ hπ hσ)
    (genericSymmetricDualLPolynomial_isPadic F ψ ν π σ hπ hσ) _).mpr
  exact genericSymmetricGammaUnit_eq_expression F ψ ν hν π σ hπ hσ

/-- The construction from actual local factors agrees with the existing
generic gamma constructor. -/
theorem genericSymmetricGammaFactor_eq_unit :
    genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ =
      genericSymmetricGammaUnit F ψ ν hν π σ hπ hσ := by
  apply Units.ext
  exact genericSymmetricGammaFactor_eq F ψ ν hν π σ hπ hσ
    (genericSymmetricGammaUnit_isPadic F ψ ν hν π σ hπ hσ)

theorem genericSymmetricGammaFactor_eq_expression :
    (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions) =
      rationalGammaExpression (LocalFactor.residueReflection F)
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).1
        (genericSymmetricEpsilonData F ψ ν hν π σ hπ hσ).2
        (genericSymmetricLPolynomial F ψ ν π σ hπ hσ)
        (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ) := by
  rw [genericSymmetricGammaFactor_eq_unit,
    genericSymmetricGammaUnit_eq_expression]

include hν hπ hσ in
/-- Nonvanishing of the displayed reflected dual denominator is a sufficient
condition for membership in the full reduced-denominator regular domain. -/
theorem mem_genericSymmetricGammaRegularDomain_of_dualPolynomial (s : ℂ)
    (hPd : (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ).eval
      (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) ≠ 0) :
    s ∈ genericSymmetricGammaRegularDomain F ψ ν hν π σ hπ hσ := by
  change RationalEvaluation.RegularAt _ _
  rw [genericSymmetricGammaFactor_eq_expression]
  apply regular_rationalGammaExpression _ _ _ _ _
    (spectralPoint_ne_zero F.canonicalTopologicalData.residueCardinality_gt_one s)
  simpa only [LocalFactor.coe_residueReflection,
    ← spectralPoint_one_sub F.canonicalTopologicalData.residueCardinality_gt_one] using hPd

/-- On the displayed polynomial domain, the existing complex gamma value is
the actual epsilon value times the original/dual polynomial ratio. -/
theorem genericSymmetricGammaValue_eq_localFactors (s : ℂ)
    (hPd : (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ).eval
      (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) ≠ 0) :
    genericSymmetricGammaValue F ψ ν hν π σ hπ hσ
      ⟨s, mem_genericSymmetricGammaRegularDomain_of_dualPolynomial
        F ψ ν hν π σ hπ hσ s hPd⟩ =
      (genericSymmetricEpsilonValue F ψ ν hν π σ hπ hσ s : ℂ) *
        (genericSymmetricLPolynomial F ψ ν π σ hπ hσ).eval
          (spectralPoint F.canonicalTopologicalData.residueCardinality s) /
        (genericSymmetricDualLPolynomial F ψ ν π σ hπ hσ).eval
          (spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s)) := by
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have href :
      (LocalFactor.residueReflection F : ℂ) /
        spectralPoint F.canonicalTopologicalData.residueCardinality s =
      spectralPoint F.canonicalTopologicalData.residueCardinality (1 - s) := by
    rw [LocalFactor.coe_residueReflection, spectralPoint_one_sub hq]
  rw [genericSymmetricGammaValue_eq, genericSymmetricGammaFactor_eq_expression,
    eval_rationalGammaExpression _ _ _ _ _
      (spectralPoint_ne_zero hq s) (by rwa [href]), href]
  rfl

end Langlands.RankinSelberg
