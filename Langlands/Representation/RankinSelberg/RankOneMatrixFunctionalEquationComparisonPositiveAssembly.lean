import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonZeroPadic
import Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationProof
import Langlands.Representation.RankinSelberg.UnequalRankUnitSpanProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws

/-!
# Assembly from a single-vector block-zero equation

The actual constant second model vector can be absorbed into the first vector,
simultaneously in the original and Weyl-transformed complementary integrals.
The analytic block-zero equation remains an explicit input.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section Algebra

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The canonical constant-one vector in the actual trivial rank-one model. -/
def rankOneTrivialModelOne (ψ : UnitaryAdditiveCharacter F) :
    (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional ψ)).toSubmodule :=
  modelMap _ (rankOneTrivialInverseFunctional ψ) (1 : ℂ)

omit [IsTopologicalRing F] in
@[simp]
theorem rankOneTrivialModelOne_apply (ψ : UnitaryAdditiveCharacter F)
    (g : Langlands.GeneralLinear (0 + 1) F) :
    (rankOneTrivialModelOne ψ).val.val g = 1 := by
  change rankOneCharacter (1 : Fˣ →* ℂˣ) g (1 : ℂ) = 1
  simp [rankOneCharacter, characterRepresentation, twist]

omit [IsTopologicalRing F] in
/-- Every actual second vector is its value at one times the canonical vector. -/
theorem rankOneTrivialModel_eq_smul_one (ψ : UnitaryAdditiveCharacter F)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional ψ)).toSubmodule) :
    f' = f'.val.val 1 • rankOneTrivialModelOne ψ := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change f'.val.val g = f'.val.val 1 * (rankOneTrivialModelOne ψ).val.val g
  rw [rankOneTrivialModelOne_apply, mul_one]
  exact rankOneTrivialModel_constant ψ _ f' g

variable [MeasurableSpace F]

omit [IsTopologicalRing F] in
private theorem integralAt_smul_left {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (c : ℂ) (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ρ (c • W) W' s =
      c * unequalRankIntegralAt j k hr ψ abv μ ρ W W' s := by
  subst r
  exact unequalRankIntegral_smul_left ψ abv j k μ ρ c W W' s

omit [IsTopologicalRing F] in
private theorem integralAt_smul_right {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (c : ℂ) (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ρ W (c • W') s =
      c * unequalRankIntegralAt j k hr ψ abv μ ρ W W' s := by
  subst r
  exact unequalRankIntegral_smul_right ψ abv j k μ ρ c W W' s

variable [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F)) (ν : AdditiveHaarMeasure F)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r π)

omit [IsTopologicalRing F] in
/-- Absorbing the second vector preserves the actual original integral at
every block and every spectral parameter, without a convergence assumption. -/
theorem unequalRankIntegralAt_rankOne_absorb (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional ψ)).toSubmodule) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (0 + 1))
        f.val f'.val s =
      unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (0 + 1))
        (f'.val.val 1 • f).val (rankOneTrivialModelOne ψ).val s := by
  have hf' := congrArg Subtype.val (rankOneTrivialModel_eq_smul_one ψ f')
  conv_lhs => rw [hf']
  exact (integralAt_smul_right j k hr ψ abv μ _ _ _ _ s).trans
    (integralAt_smul_left j k hr ψ abv μ _ _ _ _ s).symm

/-- The same absorbed vector also preserves the genuine dual integral,
including its complementary block, inverse character and block Weyl translate. -/
theorem dualUnequalRankModelIntegralAt_rankOne_absorb (hrpos : 0 < r)
    (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional ψ)).toSubmodule) (s : ℂ) :
    dualUnequalRankModelIntegralAt hrpos j k hr ψ abv μ ν π
        (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ) f f' s =
      dualUnequalRankModelIntegralAt hrpos j k hr ψ abv μ ν π
        (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
        (f'.val.val 1 • f) (rankOneTrivialModelOne ψ) s := by
  have hf' := congrArg Subtype.val (rankOneTrivialModel_eq_smul_one ψ f')
  unfold dualUnequalRankModelIntegralAt
  conv_lhs => rw [hf']
  change unequalRankIntegralAt k j _ (ψ.scale (-1)) abv μ _
      (translateWhittaker _ r (firstDualFunction ψ r f.val) (blockWeylAt 0 r hrpos))
      (f'.val.val 1 • secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s =
    unequalRankIntegralAt k j _ (ψ.scale (-1)) abv μ _
      (f'.val.val 1 • translateWhittaker _ r (firstDualFunction ψ r f.val)
        (blockWeylAt 0 r hrpos))
      (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s
  exact (integralAt_smul_right k j _ _ abv μ _ _ _ _ s).trans
    (integralAt_smul_left k j _ _ abv μ _ _ _ _ s).symm

/-- Equations for the canonical second vector extend to every actual second
vector by absorbing its scalar into the first vector. -/
theorem unequalRankBlockZeroGammaEquation_rankOne_of_one (hrpos : 0 < r)
    {q : ℕ} {G : RationalFunctions}
    (hNonzero : ∃ R ∈ unequalRankValuesAt 0 (r - 0 - 1) (by omega) q ψ abv μ
      (rectangularMeasure ν 0 (0 + 1)) π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ), R ≠ 0)
    (hEquation : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ R Rd : RationalFunctions,
        HasRationalContinuation q
          (unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ abv μ
            (rectangularMeasure ν 0 (0 + 1)) f.val (rankOneTrivialModelOne ψ).val) R ∧
        HasRationalContinuation q
          (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ abv μ ν π
            (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
            f (rankOneTrivialModelOne ψ)) Rd ∧
        GammaFunctionalEquation q 1 r G R Rd) :
    UnequalRankBlockZeroGammaEquation hrpos q ψ abv μ ν π
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ) G := by
  refine ⟨1, rankOneTrivialModel_minusOne ψ _, hNonzero, ?_⟩
  intro f f'
  obtain ⟨R, Rd, hR, hRd, hGamma⟩ := hEquation (f'.val.val 1 • f)
  refine ⟨R, Rd, ?_, ?_, hGamma⟩
  · exact RationalContinuationLinear.continuation_of_eq_on_right hR
      ⟨0, fun s _ => unequalRankIntegralAt_rankOne_absorb ψ abv μ ν π ℓ
        0 (r - 0 - 1) (by omega) f f' s⟩
  · exact RationalContinuationLinear.continuation_of_eq_on_right hRd
      ⟨0, fun s _ => dualUnequalRankModelIntegralAt_rankOne_absorb ψ abv μ ν π ℓ
        hrpos 0 (r - 0 - 1) (by omega) f f' s⟩

end Algebra

private theorem exists_ne_zero_of_one_mem_zetaSpan {S : Set RationalFunctions}
    (h : (1 : RationalFunctions) ∈ zetaSpan S) : ∃ R ∈ S, R ≠ 0 := by
  by_contra! hzero
  have hbot : zetaSpan S = ⊥ := (Submodule.span_eq_bot).mpr hzero
  rw [hbot, Submodule.mem_bot] at h
  exact one_ne_zero h

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := borel _
local instance : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0)

include hπ hℓ in
/-- Unit membership for actual unequal-rank integrals supplies a nonzero
block-zero continuation for the supplied first model and canonical second model. -/
theorem rankOne_blockZero_exists_ne_zero (k : ℕ) (hr : r = 0 + (0 + k + 1)) :
    ∃ R ∈ unequalRankValuesAt 0 k hr
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (unipotentQuotientHaar F.Carrier 0) (rectangularMeasure ν 0 (0 + 1)) π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ),
      R ≠ 0 := by
  subst r
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  let := unipotentHaar_isMulRightInvariant F.Carrier 0
  apply exists_ne_zero_of_one_mem_zetaSpan
  exact unequalRankUnitSpan.{uF, uV, 0} F F.canonicalTopologicalData 0 0 k
      ψ (unipotentQuotientHaar F.Carrier 0)
      (unipotentQuotientHaar_isCompatible F.Carrier 0) ν V ℂ π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hπ htriv ℓ
      (rankOneTrivialInverseFunctional ψ) hℓ (rankOneTrivialInverseFunctional_ne_zero ψ)

include hπ hℓ in
/-- A block-zero equation for the canonical second vector supplies the full
symmetric gamma relation, with the same multiplier, all blocks, all compatible
quotient measures and all pairs of nonzero Whittaker functionals. -/
theorem rankOneGammaFactor_of_blockZero_one (hrpos : 0 < r) (hν : IsSelfDual ψ ν)
    {G : RationalFunctions}
    (hEquation : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ R Rd : RationalFunctions,
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (unipotentQuotientHaar F.Carrier 0) (rectangularMeasure ν 0 (0 + 1))
            f.val (rankOneTrivialModelOne ψ).val) R ∧
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (unipotentQuotientHaar F.Carrier 0) ν π
            (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
            f (rankOneTrivialModelOne ψ)) Rd ∧
        GammaFunctionalEquation F.canonicalTopologicalData.residueCardinality 1 r G R Rd) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G := by
  have htriv : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    apply scalar_isOfWhittakerType_rankOne
    intro z
    refine ⟨⊤, fun g => ?_⟩
    simp [rankOneCharacter, characterRepresentation, twist]
  let := unipotentHaar_isMulRightInvariant F.Carrier 0
  have hNonzero := rankOne_blockZero_exists_ne_zero F ψ ν π hπ ℓ hℓ
    (r - 0 - 1) (by omega)
  have hZero := unequalRankBlockZeroGammaEquation_rankOne_of_one ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (unipotentQuotientHaar F.Carrier 0) ν π ℓ hrpos hNonzero hEquation
  have hFE := unequalRankGammaPropagation.{uF, uV, 0} F F.canonicalTopologicalData 0 r
    hrpos ψ (unipotentQuotientHaar F.Carrier 0)
    (unipotentQuotientHaar_isCompatible F.Carrier 0) ν hν V ℂ π
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hπ htriv ℓ
    (rankOneTrivialInverseFunctional ψ) hℓ (rankOneTrivialInverseFunctional_ne_zero ψ)
    G hZero
  have hFactor := unequalRankGammaFactor_of_equation hrpos hπ htriv hℓ
    (rankOneTrivialInverseFunctional_ne_zero ψ) hFE
  simpa only [IsPadicSymmetricGammaFactor, Nat.zero_le, ite_true,
    IsPadicPairGammaFactor, isPairGammaFactor_of_lt hrpos] using hFactor

include hπ hℓ in
/-- The normalized equation for the same actual block-zero pair yields the
specified rational gamma expression on its full reduced-denominator domain. -/
theorem rankOneGammaFactor_of_normalized_blockZero_one (hrpos : 0 < r)
    (hν : IsSelfDual ψ ν) {P PDual : Polynomial ℂ} {c : ℂˣ} {a : ℤ}
    (hPDual : PDual ≠ 0)
    (hEquation : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ R Rd : RationalFunctions,
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (unipotentQuotientHaar F.Carrier 0) (rectangularMeasure ν 0 (0 + 1))
            f.val (rankOneTrivialModelOne ψ).val) R ∧
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (unipotentQuotientHaar F.Carrier 0) ν π
            (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
            f (rankOneTrivialModelOne ψ)) Rd ∧
        NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
          P PDual 1 c 0 a R Rd) :
    IsPadicSymmetricGammaFactor F ψ ν π
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual) := by
  apply rankOneGammaFactor_of_blockZero_one F ψ ν π hπ ℓ hℓ hrpos hν
  intro f
  obtain ⟨R, Rd, hR, hRd, hN⟩ := hEquation f
  refine ⟨R, Rd, hR, hRd, ?_⟩
  intro s hs hsd hsg
  simpa only [Units.val_one, one_pow, one_mul] using
    hN.gamma_value_of_regular F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F) hPDual s hs hsd hsg

end Padic

end Langlands.RankinSelberg
