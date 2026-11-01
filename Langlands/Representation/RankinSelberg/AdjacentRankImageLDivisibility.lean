import Langlands.Representation.RankinSelberg.AdjacentRankInducedModelContinuation
import Langlands.Representation.RankinSelberg.AdjacentRankProductDenominatorBound
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuationFamily
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof

/-! Extend the actual separated product denominator bounds through the whole model image. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance imageBoundTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance imageBoundValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance imageBoundLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance imageBoundFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance imageBoundFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance imageBoundFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance imageBoundFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance imageBoundGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance imageBoundGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance imageBoundUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance imageBoundUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance imageBoundQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance imageBoundQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Every actual rectangular Schwartz test is a finite sum of the separated
square/last-column tests used by the coefficient calculation. -/
theorem adjacentRankTest_exists_sum_separated {r : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
    ∃ (N : ℕ) (A : Fin N → GodementJacquet.MatrixTestFunction r F.Carrier)
      (b : Fin N → SchwartzBruhat (Fin (r + 1) → F.Carrier)),
      Φ = ∑ i, adjacentRankSeparatedTest (A i) (b i) := by
  let Φp := Hecke.TestFunction.pullback rectangularSplit.symm Φ
  obtain ⟨N, A, b, hab⟩ := SchwartzBruhat.exists_tensor_expansion Φp
  refine ⟨N, A, b, ?_⟩
  ext M
  have h := hab (rectangularFirstColumns M) (rectangularLastColumn M)
  simpa only [Φp, Hecke.TestFunction.pullback_apply, rectangularSplit_symm_apply,
    rectangularJoin_split, Submodule.coe_sum, Finset.sum_apply,
    adjacentRankSeparatedTest, Hecke.TestFunction.pullback_apply,
    rectangularSplit_apply, SchwartzBruhat.tensor_apply] using h

/-- At zero rows, the actual nested integral is exactly the corank integral. -/
theorem corankOneIntegral_eq_zeroZero {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier)) (μ : AdditiveHaarMeasure F.Carrier)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r) (s : ℂ) :
    corankOneIntegral ψ abv ν U W' s =
      unequalRankIntegralAt 0 0 rfl ψ abv ν (rectangularMeasure μ 0 (r + 1)) U W' s := by
  change corankOneIntegral ψ abv ν U W' s =
    unequalRankIntegral ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) U W' s
  rw [UnequalRankZeroRowAssembly.zero_row_integral_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    (unequalRankIntegrand_zero_zero ψ abv U W' s 0 q).symm

private theorem corankDenominatorBound_of_separated
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
    (ℓ : glFunctionals ψ r σ)
    (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (P : Polynomial ℂ)
    (hlocal : ∀ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
      (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule),
      (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) →
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
      AdjacentRankCorankDenominatorBound F ψ ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P) :
    ∀ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankCorankDenominatorBound F ψ ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P := by
  classical
  have : SigmaCompactSpace (GeneralLinear (r + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient r F.Carrier) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (r + 1) F.Carrier)))]
    exact isSigmaCompact_range continuous_quot_mk
  have : ν.Regular := hν.regular
  have : SigmaFinite ν := inferInstance
  have : SFinite (rectangularMeasure μ 0 (r + 1)) := by
    rw [rectangularMeasure_zero_rows]
    infer_instance
  let I := adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1
  have hreal (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      ∃ U : (glCoefficientModel ψ (r + 1) π J).toSubmodule,
        ∀ g, U.val.val g = I Ψ g := by
    obtain ⟨v, hv⟩ := himage.le ⟨Ψ, rfl⟩
    exact ⟨modelMap π J v, fun g => congrFun hv g⟩
  choose L hL using hreal
  let Lmap : adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ]
      (glCoefficientModel ψ (r + 1) π J).toSubmodule :=
    { toFun := L
      map_add' := by
        intro Ψ Θ
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (L (Ψ + Θ)).val.val g = (L Ψ).val.val g + (L Θ).val.val g
        rw [hL, hL, hL]
        exact congrFun (I.map_add Ψ Θ) g
      map_smul' := by
        intro c Ψ
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (L (c • Ψ)).val.val g = c * (L Ψ).val.val g
        rw [hL, hL]
        exact congrFun (I.map_smul c Ψ) g }
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  let hA : UnequalRankAnalyticAt 0 0 rfl qF ψ abv ν
      (rectangularMeasure μ 0 (r + 1)) π τ J ℓinv :=
    unequalRankAnalytic F F.canonicalTopologicalData r 0 0 ψ ν hν μ
      VU V' π τ hπ hτinv J ℓinv hJ hℓ'
  let C := blockContinuationFamily F.canonicalTopologicalData.residueCardinality_gt_one hA
  have hC (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
      HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U.val
          (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s)
        (C U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')) := by
    exact RationalContinuationLinear.continuation_of_eq_on_right
      (blockContinuationFamily_spec F.canonicalTopologicalData.residueCardinality_gt_one
        hA U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W'))
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s⟩
  intro U W' R hR
  let CL := (C.flip (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')).comp Lmap
  have htests (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      CL Ψ ∈ Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} := by
    induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
    | tmul Φ W =>
      obtain ⟨N, A, b, hΦ⟩ := adjacentRankTest_exists_sum_separated F Φ
      rw [hΦ, TensorProduct.sum_tmul, map_sum]
      apply Submodule.sum_mem
      intro i _
      exact hlocal (A i) (b i) W (Lmap (adjacentRankSeparatedTest (A i) (b i) ⊗ₜ[ℂ] W))
        (hL _) W' _ (hC _ W')
    | add Ψ Θ hΨ hΘ =>
      rw [map_add]
      exact Submodule.add_mem _ hΨ hΘ
  have hmem : U.val.val ∈ Set.range I := by
    have hUm := U.property
    unfold glCoefficientModel coefficientModel at hUm
    obtain ⟨v, hv⟩ := hUm
    apply himage.symm.le
    exact ⟨v, congrArg Subtype.val hv⟩
  obtain ⟨Ψ, hΨ⟩ := hmem
  have hLU : Lmap Ψ = U := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact (hL Ψ g).trans (congrFun hΨ g)
  have hvalue : R = CL Ψ := by
    have heq := hR.unique F.canonicalTopologicalData.residueCardinality_gt_one (hC U W')
    simpa only [CL, LinearMap.comp_apply, LinearMap.flip_apply, hLU] using heq
  exact hvalue.symm ▸ htests Ψ

/-- The reciprocal polynomial bound on every actual pair of vectors in
specified nonzero original and inverse-character coefficient images. -/
def AdjacentRankModelCorankDenominatorBound
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (J : glFunctionals ψ (r + 1) π)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (P : Polynomial ℂ) : Prop :=
  ∀ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
    AdjacentRankCorankDenominatorBound F ψ ν U.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P

/-- Whole-function image equality extends the actual separated finite-product
bound to every actual coefficient of the same induced functional. -/
theorem adjacentRankImage_productDenominatorBound
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
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ μ σ τ P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) μ
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁) :
    AdjacentRankModelCorankDenominatorBound F ψ ν π J τ ℓ' (P₀ * P₁) := by
  apply corankDenominatorBound_of_separated F ψ μ hself ν hν σ hσ ℓ χ π hπ
    J hJ himage τ hτ ℓ' hℓ' (P₀ * P₁)
  intro Φ φ W U hU W'
  obtain ⟨φHat, hφ⟩ := (rowFourierCompatibility ψ μ (r + 1) hself).1 φ
  obtain ⟨N, B, hB⟩ := adjacentRankModel_matchedProductContinuation_exists
    F ψ μ hself σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ J hJ U hU τ hτ ℓ' hℓ' ν hν
  obtain ⟨f, M, MD, hM, -, hdata, -⟩ := hB W'
  exact adjacentRankProductContinuation_denominatorBound F ψ μ ν hν σ ℓ τ hτ
    ℓ' hℓ' W B U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
    Φ φ χ f M 1 hM hdata P₀ P₁ hP₀ hP₁

/-- A bound on one nonzero coefficient image controls all functional images
by full Whittaker type, and has precisely the required polynomial direction. -/
theorem adjacentRankModelBound_polynomialDivisibility
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    {r : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P)
    (hbound : AdjacentRankModelCorankDenominatorBound F ψ ν π J τ ℓ' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hPair : IsPairLPolynomial qF ψ abv ν μ π τ P :=
    ((isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP).2 ν hν
  have hgen : IsNormalizedGenerator
      (unequalRankZetaValues qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) π τ) P :=
    (isPairLPolynomial_of_lt (Nat.lt_succ_self r)).mp hPair 0 0 rfl
  have hspan : zetaSpan
      (unequalRankZetaValues qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) π τ) ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply Submodule.span_le.mpr
    intro R hR
    rw [unequalRankZetaValues_eq_model qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1))
      J ℓinv (hπ.eq_smul hJ) (hτinv.eq_smul hℓ')] at hR
    obtain ⟨U, hU, W', hW', -, hcont⟩ := hR
    let U0 : (glCoefficientModel ψ (r + 1) π J).toSubmodule := ⟨U, hU⟩
    let W0inv : (coefficientModel τ ℓinv).toSubmodule := ⟨W', hW'⟩
    let W0 := inverseCoefficientAsScaledStandard F ψ τ ℓinv W0inv
    have hc : HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U W' s) R :=
      RationalContinuationLinear.continuation_of_eq_on_right hcont
        ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U W' s⟩
    exact hbound U0 W0 R hc
  apply (reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mp
  apply hspan
  rw [hgen.2]
  exact Submodule.subset_span rfl

end Langlands.RankinSelberg.Padic
