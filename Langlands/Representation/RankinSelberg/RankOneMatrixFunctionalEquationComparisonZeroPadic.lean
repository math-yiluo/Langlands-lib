import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonZero
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.LocalFactor.ResidueReflection

/-!
# The full p-adic rank-one matrix-to-gamma comparison

The fixed-functional Tate passage transports to every nonzero functional and
every compatible quotient measure, using the actual normalized Haar measures.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section Functional

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The identity linear form is an inverse Whittaker functional on the
trivial rank-one representation. -/
def rankOneTrivialInverseFunctional (ψ : UnitaryAdditiveCharacter F) :
    glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ)) :=
  ⟨LinearMap.id, by rw [glInverseFunctionals_rankOne]; trivial⟩

/-- The specified functional is nonzero. -/
theorem rankOneTrivialInverseFunctional_ne_zero (ψ : UnitaryAdditiveCharacter F) :
    (rankOneTrivialInverseFunctional ψ).val ≠ 0 := by
  intro h
  have := congrArg (fun L : Module.Dual ℂ ℂ => L 1) h
  change (1 : ℂ) = 0 at this
  exact one_ne_zero this

end Functional

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : MeasurableSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := borel _
local instance : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

/-- Actual normalized matrix data for the supplied rank-one model imply the
full symmetric p-adic gamma-factor relation, uniformly in nonzero functionals
and compatible quotient measures, with the original additive Haar measure. -/
theorem rankOneMatrixFunctionalEquationComparison_zero
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType 0 (standardCharacter ψ 0) σ)
    (ℓ : glFunctionals ψ 0 σ) (hℓ : ℓ.val ≠ 0)
    {P PDual : Polynomial ℂ} {c : ℂˣ} {a : ℤ}
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
      (V := (glCoefficientModel ψ 0 σ ℓ).toSubmodule)
      (glModelRepresentation ψ 0 σ ℓ) P PDual c a) :
    IsPadicSymmetricGammaFactor F ψ ν σ
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual) := by
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  have hFE := equalRankGammaEquation_rankOne_of_matrix ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) σ hσ ℓ hℓ
    (rankOneTrivialInverseFunctional ψ) (rankOneTrivialInverseFunctional_ne_zero ψ)
    F.canonicalTopologicalData.residueCardinality_gt_one ν
    (LocalFactor.coe_residueReflection F) hdata
  rw [← unipotentQuotientHaar_zero F.Carrier] at hFE
  have hfactor := equalRankGammaFactor_of_equation hσ htriv hℓ
    (rankOneTrivialInverseFunctional_ne_zero ψ) hFE
  simpa only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true,
    IsPadicPairGammaFactor, isPairGammaFactor_self] using hfactor

end Padic

end Langlands.RankinSelberg
