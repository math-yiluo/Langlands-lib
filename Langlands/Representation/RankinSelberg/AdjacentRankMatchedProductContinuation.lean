import Langlands.Representation.RankinSelberg.AdjacentRankMatchedModelCoefficients
import Langlands.Representation.RankinSelberg.AdjacentRankProductContinuation
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-! Matched rational finite products for the original and literal dual model. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matchedContinuationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance matchedContinuationValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance matchedContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance matchedContinuationFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance matchedContinuationFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedContinuationFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance matchedContinuationFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance matchedContinuationGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance matchedContinuationGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedContinuationUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance matchedContinuationUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedContinuationQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance matchedContinuationQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Actual common-half-plane finite products and their unique rational value,
with the explicit scalar from the model-star restriction. -/
def AdjacentRankProductContinuationData {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ)
    (M : Fin N → RationalFunctions) (c : ℂ) : Prop :=
  ∃ A : Fin N → RationalFunctions,
    (∀ i, HasRationalContinuation qF
      (fun s => equalRankIntegral ψ abv ν W (B i) φ s) (A i)) ∧
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv ν U W' s ∧
      (∀ i, EqualRankConverges ψ abv ν W (B i) φ s) ∧
      (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U W' s =
        c * adjacentRankFiniteProductValue F ψ ν W B Φ φ χ f s) ∧
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s)
      (RatFunc.C c * ∑ i, A i * M i) ∧
    ∀ R, HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s) R →
      R = RatFunc.C c * ∑ i, A i * M i

private theorem corankIntegrand_smul {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (c : ℂ)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (s : ℂ) (q : LeftUnipotentQuotient r F.Carrier) :
    corankOneIntegrand ψ abv (c • U) W' s q =
      c * corankOneIntegrand ψ abv U W' s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk]
    change (c * U.val (rankInclusion 1 g)) * W'.val g *
      determinantWeight abv g (s - 1 / 2) = _
    ring

private theorem corankIntegral_smul {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier)) (c : ℂ)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (s : ℂ) :
    corankOneIntegral ψ abv ν (c • U) W' s =
      c * corankOneIntegral ψ abv ν U W' s := by
  simp only [corankOneIntegral, corankIntegrand_smul, integral_const_mul]

set_option maxHeartbeats 1600000 in
/-- A nonzero scalar in the actual coefficient convolution is retained in
the rational product by rescaling only the ambient coefficient vector. -/
theorem corankOneCoefficient_scalarProductContinuation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (ℓ : glFunctionals ψ r σ) (ℓ' : glInverseFunctionals ψ r τ)
    (ℓU : glFunctionals ψ (r + 1) π)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (hℓU : ℓU.val ≠ 0)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (B : Fin N → (coefficientModel τ ℓ').toSubmodule)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (W' : (coefficientModel τ ℓ').toSubmodule)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ)
    (Lq Lh : ℤ) (hL : AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh)
    (c : ℂˣ)
    (hc : ∀ m, sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U.val W'.val 0) m =
        (c : ℂ) * ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
          equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (B i).val φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (M : Fin N → RationalFunctions)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) Φ
      (fun h => (χ (determinant h) : ℂ) * f i h) (M i)) :
    AdjacentRankProductContinuationData F ψ ν W.val (fun i => (B i).val)
      U.val W'.val Φ φ χ f M c := by
  let U0 := (c : ℂ)⁻¹ • U
  have hU0 : (c : ℂ) • U0 = U := by
    simp [U0, smul_smul, c.ne_zero]
  have hc0 : ∀ m, sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U0.val W'.val 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (B i).val φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k) := by
    intro m
    have he : corankOneIntegrand ψ abv U0.val W'.val 0 =
        (c : ℂ)⁻¹ • corankOneIntegrand ψ abv U.val W'.val 0 :=
      funext (corankIntegrand_smul F ψ (c : ℂ)⁻¹ U.val W'.val 0)
    rw [he, sliceCoefficient_smul, hc m, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
  obtain ⟨A, hA, ⟨a, ha⟩, hcont, -⟩ :=
    corankOneCoefficient_productContinuation F ψ ν hν μ σ τ π hσ hτ hπ
      ℓ ℓ' ℓU hℓ hℓ' hℓU W B U0 W' Φ φ χ f Lq Lh hL.1 hL.2 hc0 M hM
  have hi (s : ℂ) : corankOneIntegral ψ abv ν U.val W'.val s =
      (c : ℂ) * corankOneIntegral ψ abv ν U0.val W'.val s := by
    rw [← hU0]
    exact corankIntegral_smul F ψ ν c U0.val W'.val s
  have hright (s : ℂ) (hs : a < s.re) :
      CorankOneConverges ψ abv ν U.val W'.val s ∧
      (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
      (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U.val W'.val s =
        (c : ℂ) * adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val)
          Φ φ χ f s := by
    have h := ha s hs
    have hactual : CorankOneConverges ψ abv ν U.val W'.val s := by
      rw [← hU0]
      change Integrable (corankOneIntegrand ψ abv ((c : ℂ) • U0.val) W'.val s) ν
      have he : corankOneIntegrand ψ abv ((c : ℂ) • U0.val) W'.val s =
          fun q => (c : ℂ) * corankOneIntegrand ψ abv U0.val W'.val s q :=
        funext (corankIntegrand_smul F ψ c U0.val W'.val s)
      rw [he]
      exact h.1.const_mul c
    exact ⟨hactual, h.2.1, h.2.2.1, (hi s).trans (congrArg (fun z : ℂ => (c : ℂ) * z)
      h.2.2.2)⟩
  have hactualCont : HasRationalContinuation qF
      (fun s => corankOneIntegral ψ abv ν U.val W'.val s)
      (RatFunc.C (c : ℂ) * ∑ i, A i * M i) :=
    RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul (c : ℂ) hcont) ⟨0, fun s _ => hi s⟩
  exact ⟨A, hA, ⟨a, hright⟩, hactualCont, fun R hR =>
    hR.unique F.canonicalTopologicalData.residueCardinality_gt_one hactualCont⟩

set_option maxHeartbeats 2000000 in
/-- The same finite model family gives actual original and dual finite-product
identities and their unique rational continuations. All quotient analytic
inputs follow from full Whittaker type; actual matrix values are supplied. -/
theorem adjacentRankModel_matchedProductContinuation
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
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          ∀ M MD : Fin N → RationalFunctions,
            (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
              (generalLinearHaar F.Carrier r) Φ
              (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i)) →
            (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
              (generalLinearHaar F.Carrier r) ΦD
              (fun h => (χ⁻¹ (determinant h) : ℂ) *
                GodementJacquet.coefficientIota (f i).val h) (MD i)) →
            AdjacentRankProductContinuationData F ψ ν W.val
              (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
              U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
              Φ φ χ (fun i => (f i).val) M 1 ∧
            AdjacentRankProductContinuationData F (ψ.scale (-1)) ν WD.val
              (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
              UD.val (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
              ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
              MD (adjacentRankModelStarScalar F χ r) := by
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  let σD := inverseTransposePullback σ
  let πD := inverseTransposePullback π
  let τD := inverseTransposePullback τ
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ σ ℓ)
  let ℓUD := functionalsCongr (standardCharacter_scale_neg_one ψ (r + 1)).symm
    (dualFunctional ψ π ℓU)
  let ℓ'D := dualFunctional (ψ.scale (-1)) τ ℓ'
  let WD := inverseCoefficientAsScaledStandard F ψ σD
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let UD := inverseCoefficientAsScaledStandard F ψ πD
    (dualFunctional ψ π ℓU) (dualModelLinearMap ψ π ℓU U)
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hσD : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) σD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ σ hσ
  have hπD : IsOfWhittakerType (r + 1)
      (standardCharacter (ψ.scale (-1)) (r + 1)) πD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hτD : IsOfWhittakerType r
      (inverseStandardCharacter (ψ.scale (-1)) r) τD :=
    isOfWhittakerType_inverseTransposePullback (ψ.scale (-1)) τ hτ
  have hℓD : ℓD.val ≠ 0 := dualFunctional_nonzero ψ σ ℓ hℓ
  have hℓUD : ℓUD.val ≠ 0 := dualFunctional_nonzero ψ π ℓU hℓU
  have hℓ'D : ℓ'D.val ≠ 0 := dualFunctional_nonzero (ψ.scale (-1)) τ ℓ' hℓ'
  obtain ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, hB⟩ :=
    adjacentRankModel_matchedCoefficientConvolution F ψ μ hself σ hσ ℓ χ
      Φ φ φHat hφ W U.val hU τ hτ.1 ℓ' ν hν
  refine ⟨N, B, fun W' => ?_⟩
  obtain ⟨f, hco, hcd⟩ := hB W'
  refine ⟨f, fun M MD hM hMD => ⟨?_, ?_⟩⟩
  · exact corankOneCoefficient_scalarProductContinuation F ψ ν hν μ σ τ π
      hσ hτinv hπ ℓ (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')
      ℓU hℓ hℓ' hℓU W
      (fun i => scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i))
      U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')
      Φ φ χ (fun i => (f i).val) Lq Lh hL 1 hco.2.2.2 M hM
  · exact corankOneCoefficient_scalarProductContinuation F (ψ.scale (-1)) ν hν μ
      σD τD πD hσD hτD hπD ℓD ℓ'D ℓUD hℓD hℓ'D hℓUD WD
      (fun i => dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i))
      UD (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W')
      ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
      LqD LhD hLD (χ⁻¹ (determinant (scalar (n := r + 1) (-1 : F.Carrierˣ))))
      hcd.2.2.2 MD hMD

end Langlands.RankinSelberg.Padic
