import Langlands.Representation.RankinSelberg.AdjacentRankMatchedProductContinuation
import Langlands.Representation.GodementJacquet.ModelMatrixAnalyticData
import Langlands.Representation.GodementJacquet.CoefficientTwistAndDual
import Langlands.Representation.RankinSelberg.RankOneTestReduction

/-! Actual original and dual matrix witnesses for the matched finite products. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matrixWitnessTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matrixWitnessValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matrixWitnessLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matrixWitnessFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance matrixWitnessFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matrixWitnessFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance matrixWitnessFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance matrixWitnessGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance matrixWitnessGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matrixWitnessUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance matrixWitnessUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance matrixWitnessQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance matrixWitnessQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Both literal determinant-twisted matrix functions have actual shifted
rational values. The constructed coefficient models, full type and nonzero
functionals discharge the published model-rationality theorem's hypotheses. -/
theorem exists_adjacentRankModelMatrixValues
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (ℓ : glFunctionals ψ r τ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) :
    ∃ M MD : RationalFunctions,
      GodementJacquet.HasShiftedRationalValue qF abv
        (generalLinearHaar F.Carrier r) Φ
        (fun h => (χ (determinant h) : ℂ) * f.val h) M ∧
      GodementJacquet.HasShiftedRationalValue qF abv
        (generalLinearHaar F.Carrier r) ΦD
        (fun h => (χ⁻¹ (determinant h) : ℂ) *
          GodementJacquet.coefficientIota f.val h) MD := by
  let τT := Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ
  let ℓT := determinantTwistFunctionalEquiv ψ χ τ ℓ
  have hτT : IsOfWhittakerType r (standardCharacter ψ r) τT :=
    (isOfWhittakerType_quasicharacter_twist_iff F.canonicalTopologicalData ψ χ τ).mpr hτ
  have hℓT : ℓT.val ≠ 0 := hℓ
  let hopen := quasicharacter_isOpen_ker F.canonicalTopologicalData χ
  let fT := GodementJacquet.determinantTwistModelCoefficient ψ χ hopen τ ℓ f
  let M := GodementJacquet.Padic.modelMatrixRationalValue F ψ τT hτT ℓT hℓT Φ fT
  have hM := (GodementJacquet.Padic.modelMatrixRationalValue_spec
    F ψ τT hτT ℓT hℓT Φ fT).1
  let τD := inverseTransposePullback τT
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ τT ℓT)
  have hτD : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ τT hτT
  have hℓD : ℓD.val ≠ 0 := dualFunctional_nonzero ψ τT ℓT hℓT
  let fD := GodementJacquet.iotaDeterminantTwistModelCoefficient ψ χ hopen τ ℓ f
  let MD := GodementJacquet.Padic.modelMatrixRationalValue F (ψ.scale (-1))
    τD hτD ℓD hℓD ΦD fD
  have hMD := (GodementJacquet.Padic.modelMatrixRationalValue_spec
    F (ψ.scale (-1)) τD hτD ℓD hℓD ΦD fD).1
  refine ⟨M, MD, hM, ?_⟩
  have hfD : fD.val = fun h => (χ⁻¹ (determinant h) : ℂ) *
      GodementJacquet.coefficientIota f.val h := by
    funext h
    exact GodementJacquet.iotaDeterminantTwistModelCoefficient_apply ψ χ hopen τ ℓ f h
  simpa only [hfD] using hMD

/-- Choose the two actual shifted matrix rational values on the original
and inverse-transpose determinant-twisted coefficient images. -/
def adjacentRankModelMatrixValuePair
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (ℓ : glFunctionals ψ r τ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) : RationalFunctions × RationalFunctions :=
  let h := exists_adjacentRankModelMatrixValues F ψ τ hτ ℓ hℓ χ Φ ΦD f
  ⟨h.choose, h.choose_spec.choose⟩

/-- Both components of the chosen pair continue the literal actual integrals. -/
theorem adjacentRankModelMatrixValuePair_spec
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (ℓ : glFunctionals ψ r τ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F.Carrier)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) :
    let R := adjacentRankModelMatrixValuePair F ψ τ hτ ℓ hℓ χ Φ ΦD f
    GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) Φ
      (fun h => (χ (determinant h) : ℂ) * f.val h) R.1 ∧
    GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) ΦD
      (fun h => (χ⁻¹ (determinant h) : ℂ) *
        GodementJacquet.coefficientIota f.val h) R.2 :=
  (exists_adjacentRankModelMatrixValues F ψ τ hτ ℓ hℓ χ Φ ΦD f).choose_spec.choose_spec

/-- The matched original and literal dual rational product formulas with
all actual matrix continuations supplied by the published model theorem.
The whole-function realization of the ambient vector is still explicit. -/
theorem adjacentRankModel_matchedProductContinuation_exists
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
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback π)
      (dualFunctional ψ π ℓU) (dualModelLinearMap ψ π ℓU U)
    ∃ (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ (f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'))
          (M MD : Fin N → RationalFunctions),
          (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
            (generalLinearHaar F.Carrier r) Φ
            (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i)) ∧
          (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
            (generalLinearHaar F.Carrier r) ΦD
            (fun h => (χ⁻¹ (determinant h) : ℂ) *
              GodementJacquet.coefficientIota (f i).val h) (MD i)) ∧
          AdjacentRankProductContinuationData F ψ ν W.val
            (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
            U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
            Φ φ χ (fun i => (f i).val) M 1 ∧
          AdjacentRankProductContinuationData F (ψ.scale (-1)) ν WD.val
            (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
            UD.val (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
            ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
            MD (adjacentRankModelStarScalar F χ r) := by
  classical
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  obtain ⟨N, B, hB⟩ := adjacentRankModel_matchedProductContinuation
    F ψ μ hself σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ ℓU hℓU U hU τ hτ ℓ' hℓ' ν hν
  refine ⟨N, B, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  choose M MD hM hMD using fun i =>
    exists_adjacentRankModelMatrixValues F (ψ.scale (-1)) τ hτ ℓ' hℓ' χ Φ ΦD (f i)
  exact ⟨f, M, MD, hM, hMD, hf M MD hM hMD⟩

end Langlands.RankinSelberg.Padic
