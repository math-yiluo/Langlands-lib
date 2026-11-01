import Langlands.Representation.RankinSelberg.AdjacentRankMatrixExistence
import Langlands.Representation.RankinSelberg.AdjacentRankFiniteProductFunctionalEquation
import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationProof

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matchedFEFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matchedFEValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matchedFELocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matchedFEFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance matchedFEFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedFEFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance matchedFEFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance matchedFEGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance matchedFEGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedFEUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance matchedFEUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedFEQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance matchedFEQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

set_option maxHeartbeats 800000

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Actual original and dual corank continuations with one fixed normalized equation. -/
def AdjacentRankCorankFunctionalEquation
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (P PD : Polynomial ℂ) (ζ c : ℂˣ) (m : ℤ) : Prop :=
  ∃ R RD : RationalFunctions,
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s) R ∧
    HasRationalContinuation qF (fun s => corankOneIntegral (ψ.scale (-1)) abv ν
      (firstDualFunction ψ (r + 1) U) (secondDualFunction ψ r W') s) RD ∧
    NormalizedFunctionalEquation qF P PD ζ c (r + 1) m R RD

/-- Supplied equal-rank and matrix equations combine on the same actual
matched finite family into the corank-one normalized functional equation. -/
theorem adjacentRankModel_matchedNormalizedFunctionalEquation
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (hU : ∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (P₀ PD₀ P₁ PD₁ : Polynomial ℂ) (ζ c₀ c₁ : ℂˣ) (m₀ m₁ : ℤ)
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
      P₁ PD₁ c₁ m₁)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
    AdjacentRankCorankFunctionalEquation F ψ ν U.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
      (P₀ * P₁) (PD₀ * PD₁) ζ (c₀ * c₁) (m₀ + m₁) := by
  classical
  obtain ⟨N, B, hB⟩ := adjacentRankModel_matchedProductContinuation F ψ μ hself
    σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ ℓU hℓU U hU τ hτ ℓ' hℓ' ν hν
  obtain ⟨f, hf⟩ := hB W'
  choose M MD hM hMD hMFE using fun i => hmat Φ (f i)
  let η := adjacentRankDualMatrixReflectionScalar F χ r ζ
  have hMDR (i : Fin N) : GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r)
      (adjacentRankReflectedTest (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ))
      (fun h => (χ⁻¹ (determinant h) : ℂ) * GodementJacquet.coefficientIota (f i).val h)
      (RatFunc.C (η : ℂ) * MD i) :=
    adjacentRankMatrix_reflectedRationalValue F _ _ η
      (adjacentRankDualMatrixCoefficient_minusOne F (ψ.scale (-1)) τ ℓ' ζ hζ χ (f i))
      (MD i) (hMD i)
  obtain ⟨hC, hCD⟩ := hf M (fun i => RatFunc.C (η : ℂ) * MD i) hM hMDR
  obtain ⟨A, hA, -, hR, -⟩ := hC
  obtain ⟨AD, hAD, -, hRD, -⟩ := hCD
  have hAFE (i : Fin N) : NormalizedFunctionalEquation qF P₀ PD₀ ζ c₀ r m₀ (A i) (AD i) := by
    obtain ⟨bHat, R, RD, hbHat, hval, hdval, heq⟩ :=
      heq W (scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i)) φ
    have hb : bHat = φHat := hbHat.unique hφ
    subst bHat
    have hRa : R = A i := hval.unique F.canonicalTopologicalData.residueCardinality_gt_one (hA i)
    have hRDa : RD = AD i := hdval.unique F.canonicalTopologicalData.residueCardinality_gt_one (hAD i)
    simpa only [hRa, hRDa] using heq
  refine ⟨∑ i, A i * M i,
    RatFunc.C (adjacentRankModelStarScalar F χ r) *
      ∑ i, AD i * (RatFunc.C (η : ℂ) * MD i), ?_, ?_, ?_⟩
  · simpa only [map_one, one_mul] using hR
  · exact hRD
  · exact adjacentRank_reflectedFiniteProducts_functionalEquation F χ r N A AD M MD
      P₀ PD₀ P₁ PD₁ ζ c₀ c₁ m₀ m₁ hAFE hMFE

end Langlands.RankinSelberg.Padic
