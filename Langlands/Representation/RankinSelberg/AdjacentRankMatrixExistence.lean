import Langlands.Representation.RankinSelberg.AdjacentRankMatrixFunctionalEquations

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear GodementJacquet
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance adjacentMatrixExistenceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance adjacentMatrixExistenceValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance adjacentMatrixExistenceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance adjacentMatrixExistenceT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance adjacentMatrixExistenceDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance adjacentMatrixExistenceMeasurable : MeasurableSpace F.Carrier := borel _
local instance adjacentMatrixExistenceBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance adjacentMatrixExistenceGLMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance adjacentMatrixExistenceGLBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Matrix data for any determinant twist of an irreducible full-type test. -/
private theorem exists_twistedTestMatrixFunctionalEquationData {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsOfWhittakerType r (standardCharacter ψ r) ρ)
    (hρirr : Representation.IsIrreducible ρ)
    (χ : Quasicharacter F.Carrier) :
    ∃ (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ) P PD c a := by
  have hT : IsOfWhittakerType r (standardCharacter ψ r)
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ) :=
    (isOfWhittakerType_quasicharacter_twist_iff
      F.canonicalTopologicalData ψ χ ρ).mpr hρ
  have hTirr : Representation.IsIrreducible
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ) :=
    (isIrreducible_twist_iff ((χ : F.Carrierˣ →* ℂˣ).comp determinant) ρ).mpr hρirr
  exact genericMatrixFunctionalEquation p F ψ μ hself r V _ hT hTirr

private theorem fullType_scale_neg_one {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) ρ) :
    IsOfWhittakerType r (standardCharacter ψ r) ρ := by
  apply (isOfWhittakerType_standard_iff_inverse ψ ρ).mpr
  simpa only [standardCharacter_scale_neg_one] using hρ

/-- Full Whittaker type passes to an irreducible test coefficient image. -/
private theorem adjacentTestModel_isOfWhittakerType {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (hτirr : Representation.IsIrreducible τ)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (hℓ : ℓ.val ≠ 0) :
    IsOfWhittakerType (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
      r (standardCharacter ψ r) (modelRepresentation τ ℓ) := by
  let : Representation.IsIrreducible τ := hτirr
  have e : τ.Equiv (modelRepresentation τ ℓ) := modelEquiv τ ℓ hℓ
  have hρ : IsOfWhittakerType
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
      r (standardCharacter (ψ.scale (-1)) r) (modelRepresentation τ ℓ) :=
    hτ.of_equiv e
  exact fullType_scale_neg_one F (r := r) ψ
    (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
    (modelRepresentation τ ℓ) hρ

/-- Existence of actual matrix data and literal functional-equation witnesses
on the determinant-twisted test coefficient image. -/
def AdjacentRankMatrixFunctionalEquationExistence {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (χ : Quasicharacter F.Carrier) : Prop :=
  ∃ (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
    GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
      (adjacentRankTwistedTestModel F ψ τ ℓ χ) P PD c a ∧
    AdjacentRankMatrixFunctionalEquationWitnesses F ψ μ hself τ ℓ χ P PD c a

/-- The published irreducible matrix theorem applies to the actual twisted
coefficient image. This intermediate theorem assumes irreducibility only of
the chosen test representation, not of a reducible parent input. -/
theorem exists_adjacentRankMatrixFunctionalEquationWitnesses {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (hτirr : Representation.IsIrreducible τ)
    (ℓ : glFunctionals (ψ.scale (-1)) r τ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier) :
    ∃ (P PD : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
        (adjacentRankTwistedTestModel F ψ τ ℓ χ) P PD c a ∧
      AdjacentRankMatrixFunctionalEquationWitnesses F ψ μ hself τ ℓ χ P PD c a := by
  let : Representation.IsIrreducible τ := hτirr
  have e : τ.Equiv (modelRepresentation τ ℓ) := modelEquiv τ ℓ hℓ
  have hρirr : Representation.IsIrreducible
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
      (modelRepresentation τ ℓ) :=
    (isIrreducible_iff_of_equiv e).mp hτirr
  have hρ := adjacentTestModel_isOfWhittakerType F ψ τ hτ hτirr ℓ hℓ
  obtain ⟨P, PD, c, a, hdata⟩ := exists_twistedTestMatrixFunctionalEquationData F
    (r := r) ψ μ hself
    (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ).toSubmodule)
    (modelRepresentation τ ℓ) hρ hρirr χ
  exact ⟨P, PD, c, a, hdata,
    adjacentRankMatrixFunctionalEquationWitnesses_of_data F ψ μ hself τ ℓ χ P PD c a hdata⟩

end Langlands.RankinSelberg.Padic
