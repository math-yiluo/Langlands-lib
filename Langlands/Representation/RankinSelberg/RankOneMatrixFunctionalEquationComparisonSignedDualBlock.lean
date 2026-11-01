import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualTransport
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion

/-! # Exact density, sign and quotient transport of the complementary dual block -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Conductor RankOneIwasawa
open RankOneBox AdjacentBlockReduction QuotientIntegration

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance signedDualBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance signedDualBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance signedDualBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance signedDualBlockT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance signedDualBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance signedDualBlockScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance signedDualBlockScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance signedDualBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance signedDualBlockGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance signedDualBlockGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance signedDualBlockGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)
local instance signedDualBlockUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F.Carrier) := borel _
local instance signedDualBlockUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
local instance signedDualBlockQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F.Carrier) := borel _
local instance signedDualBlockQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The literal unsigned complementary dual block on the actual GL₁ product. -/
def rankOneDualBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) : ℂ :=
  dualFunction (m + 1) W
      (blockMatrixAt m 0 (by omega) z.1 z.2 * blockWeylAt 0 (m + 1) (by omega)) *
    determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2)

/-- The density acts on the complete weighted integrand with exactly the JPSS shift. -/
theorem principalFixedBlockIntegrand_density (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) :
    weight F (m + 1) (z.1, 1) •
      principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1)) W z =
    W (blockMatrixAt m 0 (by omega) z.1 z.2 *
        rankOneSignedBlockWeyl (m + 1) (by omega)) *
      determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2) := by
  unfold principalFixedBlockIntegrand
  rw [mul_comm (determinantWeight _ _ _)]
  exact weight_smul_determinantWeight F z.1 s _

/-- Density and alternating rectangular signs preserve genuine block convergence. -/
theorem integrable_principalFixedBlockIntegrand_signedDual_iff
    (ν : AdditiveHaarMeasure F.Carrier) (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ) :
    Integrable (principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
      (rankOneSignedDualFunction (m + 1) W))
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) ↔
    Integrable (rankOneDualBlockIntegrand F m s W)
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) := by
  have hw : Measurable fun g : Langlands.GeneralLinear 1 F.Carrier =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hwp : Measurable fun z :
      Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier =>
      weight F (m + 1) (z.1, 1) := hw.comp measurable_fst
  rw [glOneMeasure, prod_withDensity_left hw.coe_nnreal_ennreal,
    integrable_withDensity_iff_integrable_smul hwp]
  have he :
      (fun z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier =>
        weight F (m + 1) (z.1, 1) •
          principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
            (rankOneSignedDualFunction (m + 1) W) z) =
      (fun z => determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2) *
        rankOneSignedDualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            rankOneSignedBlockWeyl (m + 1) (by omega))) := by
    funext z
    rw [principalFixedBlockIntegrand_density, mul_comm]
  rw [he]
  have h := integrable_rankOneSignedDualFunction_block_iff ν
    (generalLinearHaar F.Carrier 0) m abv (s - ((m + 1 : ℕ) : ℂ) / 2) W
  unfold rankOneDualBlockIntegrand
  simpa only [mul_comm] using h

/-- The two substitutions contribute no scalar to the complete block integral. -/
theorem integral_principalFixedBlockIntegrand_signedDual
    (ν : AdditiveHaarMeasure F.Carrier) (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F.Carrier → ℂ) :
    (∫ z, principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
      (rankOneSignedDualFunction (m + 1) W) z
      ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) =
    ∫ z, rankOneDualBlockIntegrand F m s W z
      ∂(generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1) := by
  have hw : Measurable fun g : Langlands.GeneralLinear 1 F.Carrier =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hwp : Measurable fun z :
      Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier =>
      weight F (m + 1) (z.1, 1) := hw.comp measurable_fst
  rw [glOneMeasure, prod_withDensity_left hw.coe_nnreal_ennreal,
    integral_withDensity_eq_integral_smul hwp]
  simp_rw [principalFixedBlockIntegrand_density]
  have h := integral_rankOneSignedDualFunction_block ν
    (generalLinearHaar F.Carrier 0) m abv (s - ((m + 1 : ℕ) : ℂ) / 2) W
  simpa only [rankOneDualBlockIntegrand, mul_comm] using h

/-- Rank transport of the actual block agrees with rank transport of the dual function. -/
theorem dualFunction_blockMatrixAt_rankCast
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (W : WhittakerFunctions ψ r) (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (a : Langlands.GeneralLinear (r + 1) F.Carrier)
    (g : Langlands.GeneralLinear 1 F.Carrier)
    (X : Matrix (Fin j) (Fin 1) F.Carrier) :
    dualFunction r W.val (blockMatrixAt j k hr g X * a) =
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) hr
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W) a)).val
          (unequalRankMatrix j k g X) := by
  subst r
  rfl

section ActualModel

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F.Carrier))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F.Carrier) (generalLinearHaar F.Carrier 0)
    (unipotentHaar F.Carrier 0) μ)

/-- The actual quotient dual integrand pulls back to the complete GL₁ integrand. -/
theorem rankOneDualBlockIntegrand_eq_quotient (s : ℂ)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) :
    rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w) z =
    unequalRankIntegrand (ψ.scale (-1)) abv m 0
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
        (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) w.val)
          (blockWeylAt 0 (m + 1) (by omega))))
      (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s z.2 (Quotient.mk _ z.1) := by
  simp only [unequalRankIntegrand_mk, secondDualFunction_apply, rankOneTrivialModelOne_apply,
    mul_one]
  unfold rankOneDualBlockIntegrand
  rw [show glModelFunction ψ (m + 1) σ ℓ w = w.val.val from rfl,
    dualFunction_blockMatrixAt_rankCast]

include hμ in
/-- Genuine convergence of the Library dual is precisely convergence on the GL₁ product. -/
theorem integrable_rankOneDualBlockIntegrand_iff (s : ℂ) :
    Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w))
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) ↔
    UnequalRankConverges (ψ.scale (-1)) abv m 0 μ (rectangularMeasure ν m 1)
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
        (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) w.val)
          (blockWeylAt 0 (m + 1) (by omega))))
      (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s := by
  rw [eq_rankOneQuotientHaar_of_isCompatible F.Carrier μ hμ, UnequalRankConverges,
    RankOneBlockConvergence.integrable_quotient_prod_iff F]
  have he := funext (rankOneDualBlockIntegrand_eq_quotient F ψ σ ℓ w s)
  rw [← he]

include hμ in
/-- Fubini and the actual rank-one quotient identify the genuine dual value. -/
theorem integral_rankOneDualBlockIntegrand (s : ℂ)
    (hi : Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w))
      ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))) :
    (∫ z, rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w) z
      ∂(generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) =
    dualUnequalRankModelIntegralAt (by omega) 0 m (by omega) ψ abv μ ν σ
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
      w (rankOneTrivialModelOne ψ) s := by
  rw [dualUnequalRankModelIntegralAt, unequalRankIntegralAt_eq_rankCast, unequalRankIntegral,
    eq_rankOneQuotientHaar_of_isCompatible F.Carrier μ hμ, integral_rankOneQuotientHaar]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with g
  apply integral_congr_ae
  filter_upwards [] with X
  exact rankOneDualBlockIntegrand_eq_quotient F ψ σ ℓ w s (g, X)

include hμ in
/-- The supplied inverse-transpose matrix data give a common genuine block half-plane. -/
theorem rankOneDualBlock_convergesOnRight_of_iota
    (hσ : IsOfWhittakerType (m + 1) (standardCharacter ψ (m + 1)) σ) (hℓ : ℓ.val ≠ 0)
    (P : Polynomial ℂ)
    (hIota : GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ) P) :
    ∃ b : ℝ, ∀ v : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ v))
          ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1)) := by
  obtain ⟨b, hb⟩ := RankOneBlockConvergence.dualBlockZero_convergesOnRight_of_iota
    F ψ ν σ ℓ (by omega) hσ hℓ μ hμ P hIota
  refine ⟨b, fun v s hs => ?_⟩
  apply (integrable_rankOneDualBlockIntegrand_iff F ψ ν σ ℓ v μ hμ s).mpr
  have he : m + 1 - 0 - 1 = m := by omega
  have H : ∃ hr : m + 1 = 0 + ((m + 1 - 0 - 1) + 0 + 1),
      UnequalRankConverges (ψ.scale (-1)) abv (m + 1 - 0 - 1) 0 μ
        (rectangularMeasure ν (m + 1 - 0 - 1) 1)
        (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) hr
          (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) v.val)
            (blockWeylAt 0 (m + 1) (by omega))))
        (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s :=
    ⟨_, hb v s hs⟩
  rw [he] at H
  exact H.choose_spec

end ActualModel

end Langlands.RankinSelberg
