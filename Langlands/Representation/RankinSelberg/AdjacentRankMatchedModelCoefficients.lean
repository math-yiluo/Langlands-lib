import Langlands.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient
import Langlands.Representation.RankinSelberg.AdjacentRankSpectralExpansion

/-! Matched actual original and model-star determinant coefficients. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matchedCoefficientFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matchedCoefficientValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matchedCoefficientLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matchedCoefficientFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance matchedCoefficientFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedCoefficientFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance matchedCoefficientFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance matchedCoefficientGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance matchedCoefficientGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedCoefficientUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance matchedCoefficientUnipotentBorel (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedCoefficientGroupSecondCountable (r : ℕ) :
    SecondCountableTopology (GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance matchedCoefficientGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance matchedCoefficientQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance matchedCoefficientQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The actual finite convolution for a supplied realized corank-one vector,
including genuine integrability of every determinant slice and factor. -/
def AdjacentRankCoefficientConvolution {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1))
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ) (c : ℂ) : Prop :=
  SliceIntegrable F.canonicalTopologicalData ν (corankOneIntegrand ψ abv U W' 0) ∧
    (∀ k i, Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
      (equalRankIntegrand ψ abv W (B i) φ 0)) ν) ∧
    (∀ j i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j
      ((r : ℂ) / 2) h * f i h) (generalLinearHaar F.Carrier r)) ∧
    ∀ m, sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U W' 0) m =
        c * ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
          equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W (B i) φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)

/-- Transfer the actual before-shell identification and a supplied outer
convolution to actual coefficients, preserving every finite witness. -/
theorem adjacentRankCoefficientConvolution_of_shell {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1))
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ) (c : ℂ)
    (hind : ∀ m q, (determinantSlice F.canonicalTopologicalData r m).indicator
      (corankOneIntegrand ψ abv U W' 0) q =
        c * ∫ h, adjacentRankBeforeShearKernel F ψ W W' Φ φ
          (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F.Carrier r)
    (hshell : ∀ m, AdjacentRankShellConvolutionAt F ψ W W' Φ φ χ ν
      Lq Lh B f m ((r : ℂ) / 2)) :
    AdjacentRankCoefficientConvolution F ψ W W' U Φ φ χ ν Lq Lh B f c := by
  classical
  have he : ∀ m, (determinantSlice F.canonicalTopologicalData r m).indicator
      (corankOneIntegrand ψ abv U W' 0) =
        fun q => c * ∫ h, adjacentRankBeforeShearKernel F ψ W W' Φ φ
          (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F.Carrier r :=
    fun m => funext (hind m)
  have hslice : SliceIntegrable F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U W' 0) := by
    intro m
    have ho := (hshell m).1.integral_prod_left
    have hi : Integrable ((determinantSlice F.canonicalTopologicalData r m).indicator
        (corankOneIntegrand ψ abv U W' 0)) ν := by
      rw [he m]
      exact ho.const_mul c
    exact (integrable_indicator_iff
      (measurableSet_determinantSlice F.canonicalTopologicalData r m)).mp hi
  refine ⟨hslice, (hshell 0).2.2.1, (hshell 0).2.2.2.1, fun m => ?_⟩
  rw [sliceCoefficient_eq_integral_indicator, he m, integral_const_mul]
  exact congrArg (fun z : ℂ => c * z) (hshell m).2.2.2.2.2

set_option maxHeartbeats 1600000 in
/-- The actual original and dual model coefficients use one finite family,
with the reflected Fourier test, inverse determinant character, and the
literal model-star scalar on the transformed side. -/
theorem adjacentRankModel_matchedCoefficientConvolution
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
      (dualFunctionEquiv ψ (r + 1) U)
    ∃ (Lq Lh LqD LhD : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh ∧
      AdjacentRankShellLowerBounds F WD.val.val ΦD φHat LqD LhD ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          AdjacentRankCoefficientConvolution F ψ W.val
            (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
            U Φ φ χ ν Lq Lh
            (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
            (fun i => (f i).val) 1 ∧
          AdjacentRankCoefficientConvolution F (ψ.scale (-1)) WD.val
            (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
            UD ΦD φHat χ⁻¹ ν LqD LhD
            (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
            (fun i => GodementJacquet.coefficientIota (f i).val)
            (adjacentRankModelStarScalar F χ r) := by
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
    (dualFunctionEquiv ψ (r + 1) U)
  obtain ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, hB⟩ :=
    adjacentRankShell_matchedFiniteConvolution F ψ σ hσ.1.1 ℓ W τ hτ ℓ'
      Φ ΦD φ φHat χ χ⁻¹ ν hν
  refine ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, ?_, ?_⟩
  · apply adjacentRankCoefficientConvolution_of_shell F ψ W.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) U Φ φ χ ν
      Lq Lh (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
      (fun i => (f i).val) 1
    · intro m q
      simpa only [one_mul] using adjacentRankModel_corankOneSlice_eq_before
        F ψ μ hself σ ℓ χ Φ φ W U hU
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) m q
    · exact fun m => (hf m ((r : ℂ) / 2)).1
  · apply adjacentRankCoefficientConvolution_of_shell F (ψ.scale (-1)) WD.val
      (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val UD ΦD φHat χ⁻¹ ν
      LqD LhD (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
      (fun i => GodementJacquet.coefficientIota (f i).val)
      (adjacentRankModelStarScalar F χ r)
    · exact fun m q => adjacentRankModelStar_corankOneSlice_eq_before
        F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W U hU
        (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val m q
    · exact fun m => (hf m ((r : ℂ) / 2)).2

end Langlands.RankinSelberg.Padic
