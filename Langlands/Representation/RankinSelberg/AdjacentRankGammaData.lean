import Langlands.Representation.RankinSelberg.AdjacentRankGammaComparison
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonProof
import Langlands.Representation.GodementJacquet.FunctionalEquationTransport
import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.Representation.Twist.IntertwiningProof
import Langlands.Representation.RankinSelberg.RankOneTestReduction

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance gammaDataFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance gammaDataValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance gammaDataLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance gammaDataFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance gammaDataFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance gammaDataFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance gammaDataFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance gammaDataGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance gammaDataGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaDataUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance gammaDataUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaDataQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance gammaDataQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

set_option maxHeartbeats 800000

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Full matrix data on a smooth full-type representation determine its
complete trivial-test gamma certificate. -/
private theorem gammaData_rankOne_of_matrix
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (P PD : Polynomial ℂ) (c : ℂˣ) (m : ℤ)
    (hdata : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      τ P PD c m) :
    IsPadicSymmetricGammaFactor F ψ μ τ (rankOneCharacter 1)
      (rationalGammaExpression (LocalFactor.residueReflection F) c m P PD) := by
  obtain ⟨ℓ, hℓ⟩ := hτ.exists_ne_zero
  let q : (⊤ : Subrepresentation τ).toRepresentation.IntertwiningMap
      (modelRepresentation τ ℓ) :=
    (modelMap τ ℓ).comp
      { toLinearMap := (⊤ : Subrepresentation τ).toSubmodule.subtype
        isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨v, hv⟩ := modelMap_surjective τ ℓ w
    exact ⟨⟨v, trivial⟩, hv⟩
  have hinc := GodementJacquet.Padic.subquotientCoefficientInclusion p F r V
    (coefficientModel τ ℓ).toSubmodule τ (modelRepresentation τ ℓ) hτ.1.1 ⊤ q hq
  exact rankOneAmbientMatrixFunctionalEquationComparison p F ψ μ hself r V τ hτ
    ℓ hℓ V τ hinc P PD c m hdata

/-- Actual block gamma factors and their product on an ambient adjacent image. -/
def AdjacentRankImageGammaFactorization
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU) : Prop :=
  ∃ G₀ G₁ : RationalFunctions,
    IsPadicSymmetricGammaFactor F ψ μ σ τ G₀ ∧
    IsPadicSymmetricGammaFactor F ψ μ τ (rankOneCharacter χ.toMonoidHom) G₁ ∧
    IsPadicSymmetricGammaFactor F ψ μ π τ (G₀ * G₁)

/-- The fixed equal-rank and matrix data exist for an irreducible chosen test,
and give complete block and ambient gamma certificates. -/
theorem adjacentRankImage_gammaFactorization_of_irreducible_test
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
    (hτirr : Representation.IsIrreducible τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0) :
    AdjacentRankImageGammaFactorization F ψ μ σ τ χ π := by
  classical
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  let ℓinv : glInverseFunctionals ψ r τ :=
    functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  have hℓinv : ℓinv.val ≠ 0 := hℓ'
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hτstd := (isOfWhittakerType_standard_iff_inverse ψ τ).mpr hτinv
  obtain ⟨ζ, c₀, m₀, P₀, PD₀, hζ, hP₀, hPD₀, heq⟩ :=
    equalRankFunctionalEquation F F.canonicalTopologicalData r ψ ν hν μ hself
      V V' σ τ hσ hτinv ℓ ℓinv hℓ hℓ'
  have hζstd : HasModelMinusOneScalar τ ℓ' ζ := by
    intro W g
    exact hζ (scaledStandardCoefficientAsInverse F ψ τ ℓ' W) g
  obtain ⟨P₁, PD₁, c₁, m₁, hdata, hmat⟩ :=
    exists_adjacentRankMatrixFunctionalEquationWitnesses F ψ μ hself τ hτ hτirr ℓ' hℓ' χ
  let g₀ := padicPairGammaFactorOfWhittakerType F ψ μ σ τ
    (padicPairGammaConstructionInput_of_whittakerType F ψ μsd r r V V' σ τ
      le_rfl hσ hτinv)
  have hG₀ : IsEqualRankGammaFactor qF ψ abv μ σ τ (g₀.val : RationalFunctions) :=
    isPairGammaFactor_self.mp g₀.property
  have hEqExpr : EqualRankGammaEquation qF ψ abv ν μ σ τ ℓ ℓinv
      (rationalGammaExpression (LocalFactor.residueReflection F) c₀ m₀ P₀ PD₀) :=
    EqualRankEpsilonEquation.gammaEquation F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F) hP₀ hPD₀
      ⟨ζ, P₀, PD₀, hζ, hP₀, hPD₀, heq⟩
  have hG₀eq : EqualRankGammaEquation qF ψ abv ν μ σ τ ℓ ℓinv
      (g₀.val : RationalFunctions) := hG₀.2.2.2 ν hν ℓ ℓinv hℓ hℓinv
  have hg₀ : (g₀.val : RationalFunctions) =
      rationalGammaExpression (LocalFactor.residueReflection F) c₀ m₀ P₀ PD₀ :=
    EqualRankGammaEquation.unique
      F.canonicalTopologicalData.residueCardinality_gt_one hℓinv hG₀eq hEqExpr
  let : Representation.IsIrreducible τ := hτirr
  let eModel : τ.Equiv (modelRepresentation τ ℓ') := modelEquiv τ ℓ' hℓ'
  let e := Langlands.twistEquiv (V := V')
    (W := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
    ((χ : F.Carrierˣ →* ℂˣ).comp determinant)
    (rho := τ) (sigma := modelRepresentation τ ℓ') eModel
  have hdataτ : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ μ
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ) P₁ PD₁ c₁ m₁ :=
    (GodementJacquet.Padic.normalizedMatrixFunctionalEquationData_equiv F ψ μ
      e P₁ PD₁ c₁ m₁).mpr hdata
  have hτT := (isOfWhittakerType_quasicharacter_twist_iff
    F.canonicalTopologicalData ψ χ τ).mpr hτstd
  have hG₁ := (rankOneGammaTwist p F ψ μ r τ χ.toMonoidHom
    (rationalGammaExpression (LocalFactor.residueReflection F) c₁ m₁ P₁ PD₁)).mp
      (gammaData_rankOne_of_matrix F ψ μ hself _ hτT P₁ PD₁ c₁ m₁ hdataτ)
  let g := padicPairGammaFactorOfWhittakerType F ψ μ π τ
    (padicPairGammaConstructionInput_of_whittakerType F ψ μsd (r + 1) r VU V' π τ
      (Nat.le_succ r) hπ hτinv)
  have hG : IsUnequalRankGammaFactor (Nat.lt_succ_self r) qF ψ abv μ π τ
      (g.val : RationalFunctions) :=
    (isPairGammaFactor_of_lt (Nat.lt_succ_self r)).mp g.property
  have hg := adjacentRankImage_gamma_eq_productExpression F ψ μ hself ν hν
    σ hσ ℓ hℓ χ π hπ J hJ himage τ hτ ℓ' hℓ' (g.val : RationalFunctions)
    (hG.2.2.2 ν hν J ℓinv hJ hℓ') P₀ PD₀ P₁ PD₁ hPD₀.polynomial_ne_zero
    hdata.2.1.2.2.polynomial_ne_zero ζ c₀ c₁ m₀ m₁ hζstd heq hmat
  have hprod : rationalGammaExpression (LocalFactor.residueReflection F)
      (c₀ * c₁) (m₀ + m₁) (P₀ * P₁) (PD₀ * PD₁) =
      rationalGammaExpression (LocalFactor.residueReflection F) c₀ m₀ P₀ PD₀ *
      rationalGammaExpression (LocalFactor.residueReflection F) c₁ m₁ P₁ PD₁ := by
    simp only [rationalGammaExpression, coe_rationalEpsilonMonomial,
      Units.val_mul, map_mul, zpow_add₀ (show (RatFunc.X : RationalFunctions) ≠ 0 from RatFunc.X_ne_zero)]
    ring
  refine ⟨(g₀.val : RationalFunctions),
    rationalGammaExpression (LocalFactor.residueReflection F) c₁ m₁ P₁ PD₁,
    (isPadicSymmetricGammaFactor_of_le le_rfl).mpr g₀.property, hG₁, ?_⟩
  apply (isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mpr
  convert g.property using 1
  rw [hg, hprod, hg₀]

end Langlands.RankinSelberg.Padic
