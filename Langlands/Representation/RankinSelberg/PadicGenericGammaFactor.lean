import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof

/-! Actual canonical p-adic gamma factors from genericity alone. -/

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

local instance padicGenericGammaNormedField : NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance padicGenericGammaValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance padicGenericGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance padicGenericGammaNonarchimedeanAddGroup : NonarchimedeanAddGroup F.Carrier :=
  valuative_nonarchimedean
local instance padicGenericGammaMeasurableSpace : MeasurableSpace F.Carrier :=
  borel F.Carrier
local instance padicGenericGammaBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩

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
/-- Genericity supplies the full canonical gamma construction input, including
the original and dual analytic conclusions and epsilon existence. -/
theorem genericPairGammaConstructionInput :
    PadicPairGammaConstructionInput F ψ ν π σ :=
  padicPairGammaConstructionInput_of_whittakerType.{uF, uV, uW}
    F ψ ⟨ν, hν⟩ r n V W π σ hnr
    (isOfWhittakerType_of_isGeneric F hπ)
    (isOfInverseWhittakerType_of_isGeneric F hσ)

/-- The actual rational-function gamma unit for a generic larger-first pair. -/
def genericPairGammaFactor : RationalFunctionsˣ :=
  (padicPairGammaFactorOfWhittakerType F ψ ν π σ
    (genericPairGammaConstructionInput F hnr ψ ν hν π σ hπ hσ)).val

/-- The complete nonvacuous integral specification for the constructed unit. -/
theorem genericPairGammaFactor_isPadic :
    IsPadicPairGammaFactor F ψ ν π σ
      (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions) :=
  (padicPairGammaFactorOfWhittakerType F ψ ν π σ
    (genericPairGammaConstructionInput F hnr ψ ν hν π σ hπ hσ)).property

/-- Every rational function satisfying the integral relation is this factor. -/
theorem genericPairGammaFactor_eq {G : RationalFunctions}
    (hG : IsPadicPairGammaFactor F ψ ν π σ G) :
    (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions) = G :=
  (genericPairGammaFactor_isPadic F hnr ψ ν hν π σ hπ hσ).unique hG

theorem isPadicPairGammaFactor_iff_eq_genericPairGammaFactor {G : RationalFunctions} :
    IsPadicPairGammaFactor F ψ ν π σ G ↔
      G = (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions) := by
  constructor
  · intro hG
    exact (genericPairGammaFactor_eq F hnr ψ ν hν π σ hπ hσ hG).symm
  · rintro rfl
    exact genericPairGammaFactor_isPadic F hnr ψ ν hν π σ hπ hσ

/-- The full regular spectral domain, using the reduced rational denominator. -/
def genericPairGammaRegularDomain : Set ℂ :=
  {s | (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions).denom.eval
    (spectralPoint F.canonicalTopologicalData.residueCardinality s) ≠ 0}

/-- The complex gamma value at a parameter in its regular spectral domain. -/
def genericPairGammaValue
    (s : genericPairGammaRegularDomain F hnr ψ ν hν π σ hπ hσ) : ℂ :=
  (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions).eval
    (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s.val)

@[simp] theorem genericPairGammaValue_eq
    (s : genericPairGammaRegularDomain F hnr ψ ν hν π σ hπ hσ) :
    genericPairGammaValue F hnr ψ ν hν π σ hπ hσ s =
      (genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ : RationalFunctions).eval
        (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s.val) :=
  rfl

end Ordered

section Symmetric

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : AdditiveHaarMeasure F.Carrier) (hν : IsSelfDual ψ ν)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
  (hπ : Whittaker.IsGeneric ψ r π) (hσ : Whittaker.IsGeneric ψ n σ)

include hν hπ hσ in
/-- Genericity supplies the symmetric construction input in either rank order. -/
theorem genericSymmetricGammaConstructionInput :
    PadicSymmetricGammaConstructionInput F ψ ν π σ :=
  whittakerTypeGammaConstructionInput.{uF, uV, uW} p F ψ ⟨ν, hν⟩
    r n V W π σ
    (isOfWhittakerType_of_isGeneric F hπ) (isOfWhittakerType_of_isGeneric F hσ)

/-- The actual gamma unit in either rank order, with the larger rank first. -/
def genericSymmetricGammaFactor : RationalFunctionsˣ :=
  if hnr : n ≤ r then
    genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ
  else
    genericPairGammaFactor F (Nat.le_of_lt (Nat.lt_of_not_ge hnr)) ψ ν hν σ π hσ hπ

theorem genericSymmetricGammaFactor_of_le (hnr : n ≤ r) :
    genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ =
      genericPairGammaFactor F hnr ψ ν hν π σ hπ hσ := by
  simp only [genericSymmetricGammaFactor, dite_eq_left hnr]

theorem genericSymmetricGammaFactor_of_lt (hrn : r < n) :
    genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ =
      genericPairGammaFactor F hrn.le ψ ν hν σ π hσ hπ := by
  simp only [genericSymmetricGammaFactor, dite_eq_right (Nat.not_le.mpr hrn)]

/-- The full existing symmetric gamma relation holds for the constructed unit. -/
theorem genericSymmetricGammaFactor_isPadic :
    IsPadicSymmetricGammaFactor F ψ ν π σ
      (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions) := by
  by_cases hnr : n ≤ r
  · rw [genericSymmetricGammaFactor_of_le F ψ ν hν π σ hπ hσ hnr]
    exact (isPadicSymmetricGammaFactor_of_le hnr).mpr
      (genericPairGammaFactor_isPadic F hnr ψ ν hν π σ hπ hσ)
  · have hrn := Nat.lt_of_not_ge hnr
    rw [genericSymmetricGammaFactor_of_lt F ψ ν hν π σ hπ hσ hrn]
    exact (isPadicSymmetricGammaFactor_of_lt hrn).mpr
      (genericPairGammaFactor_isPadic F hrn.le ψ ν hν σ π hσ hπ)

theorem genericSymmetricGammaFactor_eq {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν π σ G) :
    (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions) = G :=
  (genericSymmetricGammaFactor_isPadic F ψ ν hν π σ hπ hσ).unique hG

theorem isPadicSymmetricGammaFactor_iff_eq_genericSymmetricGammaFactor
    {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π σ G ↔
      G = (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions) := by
  constructor
  · intro hG
    exact (genericSymmetricGammaFactor_eq F ψ ν hν π σ hπ hσ hG).symm
  · rintro rfl
    exact genericSymmetricGammaFactor_isPadic F ψ ν hν π σ hπ hσ

/-- Agreement with the existing certified symmetric constructor at the derived input. -/
theorem genericSymmetricGammaFactor_eq_padicSymmetricGammaFactorOfWhittakerType :
    genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ =
      (padicSymmetricGammaFactorOfWhittakerType F ψ ν π σ
        (genericSymmetricGammaConstructionInput F ψ ν hν π σ hπ hσ)).val := by
  apply Units.ext
  exact genericSymmetricGammaFactor_eq F ψ ν hν π σ hπ hσ
    (padicSymmetricGammaFactorOfWhittakerType F ψ ν π σ
      (genericSymmetricGammaConstructionInput F ψ ν hν π σ hπ hσ)).property

/-- The symmetric factor's full regular spectral domain. -/
def genericSymmetricGammaRegularDomain : Set ℂ :=
  {s | (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions).denom.eval
    (spectralPoint F.canonicalTopologicalData.residueCardinality s) ≠ 0}

/-- The symmetric complex gamma value on the regular spectral domain. -/
def genericSymmetricGammaValue
    (s : genericSymmetricGammaRegularDomain F ψ ν hν π σ hπ hσ) : ℂ :=
  (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions).eval
    (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s.val)

@[simp] theorem genericSymmetricGammaValue_eq
    (s : genericSymmetricGammaRegularDomain F ψ ν hν π σ hπ hσ) :
    genericSymmetricGammaValue F ψ ν hν π σ hπ hσ s =
      (genericSymmetricGammaFactor F ψ ν hν π σ hπ hσ : RationalFunctions).eval
        (RingHom.id ℂ) (spectralPoint F.canonicalTopologicalData.residueCardinality s.val) :=
  rfl

end Symmetric

end Langlands.RankinSelberg
