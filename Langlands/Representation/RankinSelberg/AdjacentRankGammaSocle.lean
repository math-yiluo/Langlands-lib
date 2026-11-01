import Langlands.Representation.RankinSelberg.AdjacentRankGammaData
import Langlands.Representation.RankinSelberg.SubmodelGammaComparison

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance gammaSocleFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance gammaSocleValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance gammaSocleLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance gammaSocleFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance gammaSocleFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance gammaSocleFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance gammaSocleFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance gammaSocleGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance gammaSocleGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaSocleUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance gammaSocleUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance gammaSocleQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance gammaSocleQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

set_option maxHeartbeats 800000

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

private theorem gammaSocle_characterCongr_le
    {G : Type*} [Group G] {N : Subgroup G} {θ θ' : N →* ℂˣ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {ℓ : functionals N θ ρ} {ℓ' : functionals N θ τ}
    (hc : θ = θ') (hM : coefficientModel ρ ℓ ≤ coefficientModel τ ℓ') :
    coefficientModel ρ (functionalsCongr hc ℓ) ≤
      coefficientModel τ (functionalsCongr hc ℓ') := by
  subst θ'
  exact hM

private theorem gammaSocle_characterChange_le
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W}
    {ℓ : glFunctionals ψ r ρ} {ℓ' : glFunctionals ψ r τ}
    (a : F.Carrierˣ) (hM : coefficientModel ρ ℓ ≤ coefficientModel τ ℓ') :
    coefficientModel ρ (characterChangeFunctional ψ ρ a ℓ) ≤
      coefficientModel τ (characterChangeFunctional ψ τ a ℓ') := by
  unfold coefficientModel at hM ⊢
  rintro f ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := hM (show coefficientMap ρ ℓ v ∈ (coefficientMap ρ ℓ).range from ⟨v, rfl⟩)
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext g
  change (coefficientMap τ (characterChangeFunctional ψ τ a ℓ') w).val g =
    (coefficientMap ρ (characterChangeFunctional ψ ρ a ℓ) v).val g
  rw [characterChangeFunctional_coefficient, characterChangeFunctional_coefficient]
  exact congrArg (fun f => f.val (characterChangeElement a r * g)) hw

private theorem gammaSocle_characterChange_ne_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r ρ) (hℓ : ℓ.val ≠ 0) (a : F.Carrierˣ) :
    (characterChangeFunctional ψ ρ a ℓ).val ≠ 0 := by
  intro hz
  have hzero : characterChangeFunctionalEquiv ψ ρ a ℓ = 0 := Subtype.ext hz
  have : ℓ = 0 := (characterChangeFunctionalEquiv ψ ρ a).injective (by simpa using hzero)
  exact hℓ (congrArg Subtype.val this)

/-- The irreducible-test construction extends to every original full-type test
through its actual generic socle and nested coefficient models. -/
theorem adjacentRankImage_gammaFactorization
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
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0) :
    AdjacentRankImageGammaFactorization F ψ μ σ τ χ π := by
  classical
  let μsd : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨μ, hself⟩
  let : AddCommGroup (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule :=
    (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule.addCommGroup
  obtain ⟨S, hS, hSirr, -, hStype⟩ :=
    modelGenericSocle p inferInstance F (ψ.scale (-1)) r V' τ hτ ℓ' hℓ'
  let ev : glFunctionals (ψ.scale (-1)) r (V := S.toSubmodule) S.toRepresentation :=
    submodelEvaluation τ ℓ' S
  have hev : ev.val ≠ 0 := submodelEvaluation_ne_zero τ ℓ' S hS
  have hMs : coefficientModel (V := S.toSubmodule) S.toRepresentation ev ≤
      coefficientModel τ ℓ' := coefficientModel_submodelEvaluation_le τ ℓ' S
  obtain ⟨G₀, G₁, hG₀, hG₁, hG⟩ :=
    adjacentRankImage_gammaFactorization_of_irreducible_test F ψ μ hself ν hν
      σ hσ ℓ hℓ χ π hπ J hJ himage
      (V' := S.toSubmodule) S.toRepresentation hStype hSirr ev hev
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hτstd := (isOfWhittakerType_standard_iff_inverse ψ τ).mpr hτinv
  let g₀ := padicSymmetricGammaFactorOfWhittakerType F ψ μ σ τ
    (whittakerTypeGammaConstructionInput p F ψ μsd r r V V' σ τ hσ hτstd)
  let g₁ := padicSymmetricGammaFactorOfWhittakerType F ψ μ τ
    (rankOneCharacter χ.toMonoidHom)
    (whittakerTypeGammaConstructionInput p F ψ μsd r 0 V' ℂ τ
      (rankOneCharacter χ.toMonoidHom) hτstd (rankOneCharacter_isOfWhittakerType p F ψ χ))
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ μ π τ
    (whittakerTypeGammaConstructionInput p F ψ μsd (r + 1) r VU V' π τ hπ hτstd)
  let ℓinv : glInverseFunctionals ψ r τ :=
    functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  let evinv : glInverseFunctionals ψ r (V := S.toSubmodule) S.toRepresentation :=
    functionalsCongr (standardCharacter_scale_neg_one ψ r) ev
  have hℓinv : ℓinv.val ≠ 0 := hℓ'
  have hevinv : evinv.val ≠ 0 := hev
  have hMinv : coefficientModel (V := S.toSubmodule) S.toRepresentation evinv ≤
      coefficientModel τ ℓinv :=
    gammaSocle_characterCongr_le (standardCharacter_scale_neg_one ψ r) hMs
  have hg₀ : G₀ = (g₀.val : RationalFunctions) :=
    IsPairGammaFactor.eq_of_model_le F.canonicalTopologicalData.residueCardinality_gt_one
      hℓ hevinv hℓ hℓinv le_rfl hMinv
      ((isPadicSymmetricGammaFactor_of_le le_rfl).mp hG₀)
      ((isPadicSymmetricGammaFactor_of_le le_rfl).mp g₀.property)
  have hg : G₀ * G₁ = (g.val : RationalFunctions) :=
    IsPairGammaFactor.eq_of_model_le F.canonicalTopologicalData.residueCardinality_gt_one
      hJ hevinv hJ hℓinv le_rfl hMinv
      ((isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mp hG)
      ((isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mp g.property)
  have hc : standardCharacter ((ψ.scale (-1)).scale (-1)) r = standardCharacter ψ r := by
    rw [UnitaryAdditiveCharacter.scale_scale, neg_one_mul, neg_neg,
      UnitaryAdditiveCharacter.scale_one]
  let ℓstd : glFunctionals ψ r τ :=
    functionalsCongr hc (characterChangeFunctional (ψ.scale (-1)) τ (-1) ℓ')
  let evstd : glFunctionals ψ r (V := S.toSubmodule) S.toRepresentation :=
    functionalsCongr hc
      (characterChangeFunctional (ψ.scale (-1)) (V := S.toSubmodule) S.toRepresentation (-1) ev)
  have hℓstd : ℓstd.val ≠ 0 := gammaSocle_characterChange_ne_zero F _ τ ℓ' hℓ' (-1)
  have hevstd : evstd.val ≠ 0 :=
    gammaSocle_characterChange_ne_zero F _ (V := S.toSubmodule) S.toRepresentation ev hev (-1)
  have hMstd : coefficientModel (V := S.toSubmodule) S.toRepresentation evstd ≤
      coefficientModel τ ℓstd :=
    gammaSocle_characterCongr_le hc (gammaSocle_characterChange_le F _ (-1) hMs)
  obtain ⟨ℓχ, hℓχ⟩ :=
    ((isOfWhittakerType_standard_iff_inverse ψ (rankOneCharacter χ.toMonoidHom)).mp
      (rankOneCharacter_isOfWhittakerType p F ψ χ)).exists_ne_zero
  have hg₁ : G₁ = (g₁.val : RationalFunctions) :=
    IsPairGammaFactor.eq_of_model_le F.canonicalTopologicalData.residueCardinality_gt_one
      hevstd hℓχ hℓstd hℓχ hMstd le_rfl
      ((isPadicSymmetricGammaFactor_of_le (Nat.zero_le r)).mp hG₁)
      ((isPadicSymmetricGammaFactor_of_le (Nat.zero_le r)).mp g₁.property)
  refine ⟨(g₀.val : RationalFunctions), (g₁.val : RationalFunctions),
    g₀.property, g₁.property, ?_⟩
  rw [hg₀, hg₁] at hg
  rw [hg]
  exact g.property

end Langlands.RankinSelberg.Padic
