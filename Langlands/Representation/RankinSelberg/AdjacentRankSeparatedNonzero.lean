import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility

/-! Nonzero separated continuations in the actual adjacent model image. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance separatedNonzeroTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance separatedNonzeroValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance separatedNonzeroLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance separatedNonzeroFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance separatedNonzeroFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance separatedNonzeroFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance separatedNonzeroFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance separatedNonzeroGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance separatedNonzeroGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance separatedNonzeroUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance separatedNonzeroUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance separatedNonzeroQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance separatedNonzeroQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- A genuinely nonzero actual continuation on a separated ambient coefficient. -/
def AdjacentRankNonzeroSeparatedContinuation
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
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) : Prop :=
  ∃ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
    (R : RationalFunctions),
    (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) ∧
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) R ∧ R ≠ 0

/-- Whole-function image equality and a nonzero corank continuation force
one separated coefficient to have a nonzero continuation. -/
theorem adjacentRankImage_exists_nonzeroSeparatedContinuation
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
    (hnonzero : ∃ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
      (R : RationalFunctions),
      HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) R ∧ R ≠ 0) :
    AdjacentRankNonzeroSeparatedContinuation F ψ μ hself ν σ ℓ χ π J τ ℓ' := by
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
  obtain ⟨U, W', R, hR, hR0⟩ := hnonzero
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
  let CL := (C.flip (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')).comp Lmap
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
  have hex : ∃ (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
      (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule),
      CL (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) ≠ 0 := by
    by_contra! hzero
    have htests (Θ : adjacentRankTestSpace ψ σ ℓ) : CL Θ = 0 := by
      induction Θ using adjacentRankTestSpace_induction ψ σ ℓ with
      | tmul Φ W =>
        obtain ⟨N, A, b, hΦ⟩ := adjacentRankTest_exists_sum_separated F Φ
        rw [hΦ, TensorProduct.sum_tmul, map_sum]
        exact Finset.sum_eq_zero fun i _ => hzero (A i) (b i) W
      | add Θ Λ hΘ hΛ => rw [map_add, hΘ, hΛ, add_zero]
    exact hR0 (hvalue.trans (htests Ψ))
  obtain ⟨Φ, φ, W, hnonzero⟩ := hex
  exact ⟨Φ, φ, W, Lmap (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W), W',
    CL (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W), hL _, hC _ W', hnonzero⟩

end Langlands.RankinSelberg.Padic
