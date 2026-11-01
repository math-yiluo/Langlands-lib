import Langlands.Representation.RankinSelberg.AdjacentRankSeparatedNonzero
import Langlands.Representation.RankinSelberg.AdjacentRankMatchedFunctionalEquation
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance gammaComparisonFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance gammaComparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance gammaComparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance gammaComparisonFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance gammaComparisonFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance gammaComparisonFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance gammaComparisonFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance gammaComparisonGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance gammaComparisonGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaComparisonUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance gammaComparisonUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaComparisonQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance gammaComparisonQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

set_option maxHeartbeats 800000

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- The block Weyl element is the identity in corank one. -/
theorem adjacentRank_blockWeyl_eq_one (r : ℕ) :
    blockWeylAt (F := F.Carrier) r (r + 1) (Nat.lt_succ_self r) = 1 := by
  have hw : weylLong (r + 1 - r) F.Carrier = 1 := by
    have hdim : r + 1 - r = 1 := by omega
    rw [hdim, RankOneGammaTwist.weylLong_one]
  unfold blockWeylAt
  rw [hw]
  change GeneralLinear.reindex _ (blockSum 1) = 1
  rw [map_one, map_one]

/-- In corank one the dual zero-block integral is the literal dual corank integral. -/
theorem adjacentRank_dualUnequalRankIntegral_eq_corank
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier)) (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (J : glFunctionals ψ (r + 1) π) (ℓ' : glInverseFunctionals ψ r τ)
    (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
    (W' : (coefficientModel τ ℓ').toSubmodule) (s : ℂ) :
    dualUnequalRankModelIntegralAt (Nat.lt_succ_self r) 0 0 rfl ψ abv ν μ
      π τ J ℓ' U W' s =
    corankOneIntegral (ψ.scale (-1)) abv ν
      (firstDualFunction ψ (r + 1) U.val) (secondDualFunction ψ r W'.val) s := by
  unfold dualUnequalRankModelIntegralAt
  rw [adjacentRank_blockWeyl_eq_one F]
  have ht : translateWhittaker (ψ.scale (-1)) (r + 1)
      (firstDualFunction ψ (r + 1) U.val) 1 = firstDualFunction ψ (r + 1) U.val := by
    apply Subtype.ext
    funext g
    exact congrArg (firstDualFunction ψ (r + 1) U.val).val (mul_one g)
  rw [ht]
  exact (corankOneIntegral_eq_zeroZero F (ψ.scale (-1)) ν μ _ _ s).symm

/-- Fixed normalized equations on every separated coefficient of the actual model image. -/
def AdjacentRankSeparatedNormalizedEquations
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (J : glFunctionals ψ (r + 1) π)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (P PD : Polynomial ℂ) (ζ c : ℂˣ) (m : ℤ) : Prop :=
  ∀ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule),
    (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) →
    ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
      AdjacentRankCorankFunctionalEquation F ψ ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P PD ζ c m

/-- One nonzero separated integral identifies an existing ambient gamma factor. -/
theorem adjacentRankImage_gamma_eq_expression_of_separated
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (G : RationalFunctions)
    (hG : UnequalRankGammaEquation (Nat.lt_succ_self r) qF ψ abv ν μ π τ J
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ') G)
    (P PD : Polynomial ℂ) (hPD : PD ≠ 0) (ζ c : ℂˣ) (m : ℤ)
    (hζ : HasModelMinusOneScalar τ ℓ' ζ)
    (hsep : AdjacentRankSeparatedNormalizedEquations F ψ μ hself ν σ ℓ χ π J τ ℓ'
      P PD ζ c m) :
    G = rationalGammaExpression (LocalFactor.residueReflection F) c m P PD := by
  classical
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  obtain ⟨ζG, hζG, hall⟩ := hG
  have hζinv : HasModelMinusOneScalar τ ℓinv ζ := by
    intro W' g
    exact hζ (inverseCoefficientAsScaledStandard F ψ τ ℓinv W') g
  have hℓinv : ℓinv.val ≠ 0 := hℓ'
  have heqζ : ζG = ζ := hζG.unique hℓinv hζinv
  subst ζG
  obtain ⟨⟨R0, hRmem, hR0⟩, hFE⟩ := hall 0 0 rfl
  rw [unequalRankValuesAt_eq] at hRmem
  obtain ⟨U0, W0inv, hRcont⟩ := hRmem
  have hnonzero : ∃ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
      (R : RationalFunctions),
      HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) R ∧ R ≠ 0 := by
    refine ⟨U0, inverseCoefficientAsScaledStandard F ψ τ ℓinv W0inv, R0, ?_, hR0⟩
    exact RationalContinuationLinear.continuation_of_eq_on_right hRcont
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U0.val W0inv.val s⟩
  obtain ⟨Φ, φ, W, U, W', R, hU, hR, hR0⟩ :=
    adjacentRankImage_exists_nonzeroSeparatedContinuation F ψ μ hself ν hν σ hσ ℓ χ
      π hπ J hJ himage τ hτ ℓ' hℓ' hnonzero
  obtain ⟨RA, RDA, hRA, hRDA, hGA⟩ :=
    hFE U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')
  have hRAc : HasRationalContinuation qF
      (fun s => corankOneIntegral ψ abv ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) RA :=
    RationalContinuationLinear.continuation_of_eq_on_right hRA
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s⟩
  have hRDAc : HasRationalContinuation qF
      (fun s => corankOneIntegral (ψ.scale (-1)) abv ν
        (firstDualFunction ψ (r + 1) U.val)
        (secondDualFunction ψ r (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)) s)
      RDA :=
    RationalContinuationLinear.continuation_of_eq_on_right hRDA
      ⟨0, fun s _ => (adjacentRank_dualUnequalRankIntegral_eq_corank F ψ ν μ π τ J ℓinv U
        (scaledStandardCoefficientAsInverse F ψ τ ℓ' W') s).symm⟩
  obtain ⟨RB, RDB, hRB, hRDB, hNB⟩ := hsep Φ φ W U hU W'
  have hRAeq : RA = R := hRAc.unique F.canonicalTopologicalData.residueCardinality_gt_one hR
  have hRBeq : RB = R := hRB.unique F.canonicalTopologicalData.residueCardinality_gt_one hR
  have hRDeq : RDB = RDA := hRDB.unique F.canonicalTopologicalData.residueCardinality_gt_one hRDAc
  rw [hRAeq] at hGA
  rw [hRBeq, hRDeq] at hNB
  exact hGA.gamma_unique F.canonicalTopologicalData.residueCardinality_gt_one hR0
    (hNB.gamma_value_of_regular F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F) hPD)

/-- The supplied fixed-data block equations identify the actual ambient gamma
factor without extending a normalized equation to the whole model image. -/
theorem adjacentRankImage_gamma_eq_productExpression
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0) (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (G : RationalFunctions)
    (hG : UnequalRankGammaEquation (Nat.lt_succ_self r) qF ψ abv ν μ π τ J
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ') G)
    (P₀ PD₀ P₁ PD₁ : Polynomial ℂ) (hPD₀ : PD₀ ≠ 0) (hPD₁ : PD₁ ≠ 0)
    (ζ c₀ c₁ : ℂˣ) (m₀ m₁ : ℤ)
    (hζ : HasModelMinusOneScalar τ ℓ' ζ)
    (heq : ∀ (A : (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (B : (coefficientModel τ
        (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')).toSubmodule)
      (b : SchwartzBruhat (Fin (r + 1) → F.Carrier)),
      ∃ (bHat : SchwartzBruhat (Fin (r + 1) → F.Carrier)) (R RD : RationalFunctions),
        IsRowFourierPair ψ μ b bHat ∧
        HasRationalContinuation qF
          (equalRankModelIntegral ψ abv ν σ τ ℓ
            (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ') A B b) R ∧
        HasRationalContinuation qF
          (dualEqualRankModelIntegral ψ abv ν σ τ ℓ
            (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ') A B bHat) RD ∧
        NormalizedFunctionalEquation qF P₀ PD₀ ζ c₀ r m₀ R RD)
    (hmat : AdjacentRankMatrixFunctionalEquationWitnesses F ψ μ hself τ ℓ' χ
      P₁ PD₁ c₁ m₁) :
    G = rationalGammaExpression (LocalFactor.residueReflection F)
      (c₀ * c₁) (m₀ + m₁) (P₀ * P₁) (PD₀ * PD₁) := by
  apply adjacentRankImage_gamma_eq_expression_of_separated F ψ μ hself ν hν
    σ hσ ℓ χ π hπ J hJ himage τ hτ ℓ' hℓ' G hG
    (P₀ * P₁) (PD₀ * PD₁) (mul_ne_zero hPD₀ hPD₁) ζ (c₀ * c₁) (m₀ + m₁) hζ
  intro Φ φ W U hU W'
  obtain ⟨φHat, hφ⟩ := (rowFourierCompatibility ψ μ (r + 1) hself).1 φ
  exact adjacentRankModel_matchedNormalizedFunctionalEquation F ψ μ hself
    σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ J hJ U hU τ hτ ℓ' hℓ'
    ν hν P₀ PD₀ P₁ PD₁ ζ c₀ c₁ m₀ m₁ hζ heq hmat W'

end Langlands.RankinSelberg.Padic
