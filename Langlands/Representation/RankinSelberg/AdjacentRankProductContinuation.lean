import Langlands.Representation.RankinSelberg.AdjacentRankFiniteProducts
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.Representation.GodementJacquet.FunctionalEquationProducts

/-! Actual coefficient-model convergence and continuation of the finite products. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped BigOperators

universe uF uV uW uU

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance continuationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance continuationFieldValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance continuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance continuationFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance continuationFieldTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance continuationFieldMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance continuationFieldBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance continuationGroupMeasurableSpace (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance continuationGroupBorelSpace (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance continuationUnipotentMeasurableSpace (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance continuationUnipotentBorelSpace (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance continuationQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance continuationQuotientBorelSpace (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
  {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]

set_option maxHeartbeats 800000 in
/-- Recast a vector in the actual scaled-character coefficient image as a vector
in the inverse-character image of the same transported functional. -/
def scaledStandardCoefficientAsInverse
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
    (coefficientModel τ
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')).toSubmodule :=
  ⟨InducedTailIntermediate.scaledStandardAsInverse ψ W'.val, by
    obtain ⟨v, hv⟩ := W'.property
    refine ⟨v, Subtype.ext ?_⟩
    exact congrArg (fun w : WhittakerFunctions (ψ.scale (-1)) r => w.val) hv⟩

/-- The zero-row analytic theorem supplies actual corank-one convergence for
coefficient vectors of full Whittaker-type representations. -/
theorem corankOneCoefficient_convergesOnRight
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (ℓ' : glInverseFunctionals ψ r τ)
    (hℓU : ℓU.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (W' : (coefficientModel τ ℓ').toSubmodule) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv ν U.val W'.val s := by
  have han := unequalRankAnalytic.{uF, uU, uW} F F.canonicalTopologicalData r 0 0
    ψ ν hν μ VU V' π τ hπ hτ ℓU ℓ' hℓU hℓ'
  obtain ⟨a, ha⟩ := han.1 U W'
  refine ⟨a, fun s hs => ?_⟩
  have hc := (UnequalRankZeroRowAssembly.zero_row_converges_iff ψ abv 0 ν μ
    U.val W'.val s).mp (ha s hs)
  unfold CorankOneConverges
  exact hc.congr (Filter.Eventually.of_forall fun q =>
    unequalRankIntegrand_zero_zero ψ abv U.val W'.val s 0 q)

/-- Full Whittaker type discharges the quotient analytic inputs in the finite
product formula. Only actual shifted matrix values remain analytic premises. -/
theorem corankOneCoefficient_productContinuation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F.Carrier) VU)
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
    (f : Fin N → Langlands.GeneralLinear (r + 1) F.Carrier → ℂ)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier))
    (hLh : ∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
      Lh ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier))
    (hc : ∀ m : ℤ, sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U.val W'.val 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (B i).val φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (M : Fin N → RationalFunctions)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F.Carrier r) Φ
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h) (M i)) :
    ∃ A : Fin N → RationalFunctions,
      (∀ i, HasRationalContinuation qF
        (fun s => equalRankIntegral ψ abv ν W.val (B i).val φ s) (A i)) ∧
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        CorankOneConverges ψ abv ν U.val W'.val s ∧
        (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
        (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
          (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) ∧
        corankOneIntegral ψ abv ν U.val W'.val s =
          adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val)
            Φ φ χ f s) ∧
      HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val W'.val s)
        (∑ i, A i * M i) ∧
      ∀ R, HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U.val W'.val s) R →
        R = ∑ i, A i * M i := by
  classical
  have han := equalRankAnalytic.{uF, uV, uW} F F.canonicalTopologicalData r
    ψ ν hν V V' σ τ hσ hτ ℓ ℓ' hℓ hℓ'
  obtain ⟨aU, haU⟩ := corankOneCoefficient_convergesOnRight F ψ ν hν μ
    π τ hπ hτ ℓU ℓ' hℓU hℓ' U W'
  obtain ⟨aW, haW⟩ := UnequalRankReduction.finite_common_bound
    (fun i s => EqualRankConverges ψ abv ν W.val (B i).val φ s)
    (fun i => han.1 W (B i) φ)
  obtain ⟨aM, haM⟩ := UnequalRankReduction.finite_common_bound
    (fun i s => GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h))
    (fun i => (hM i).1)
  let a := max aU (max aW aM)
  have hright (s : ℂ) (hs : a < s.re) :
      CorankOneConverges ψ abv ν U.val W'.val s ∧
      (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
      (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U.val W'.val s =
        adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val) Φ φ χ f s := by
    have hU := haU s ((le_max_left _ _).trans_lt hs)
    have hW := haW s ((le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hs)
    have hf := haM s ((le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hs)
    exact ⟨hU, hW, hf, corankOneIntegral_eq_finiteProducts_of_coefficients F ψ ν
      W.val (fun i => (B i).val) U.val W'.val Φ φ χ f Lq Lh hLq hLh hc s hU hW hf⟩
  choose A hA using fun i : Fin N => han.2.1 W (B i) φ
  have hcont : HasRationalContinuation qF
      (fun s => corankOneIntegral ψ abv ν U.val W'.val s) (∑ i, A i * M i) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right
      (GodementJacquet.hasRationalContinuation_sum_mul Finset.univ
        (fun i s => equalRankIntegral ψ abv ν W.val (B i).val φ s)
        (fun i s => GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
          (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h))
        A M (fun i _ => hA i) (fun i _ => (hM i).2))
    exact ⟨a, fun s hs => (hright s hs).2.2.2⟩
  exact ⟨A, hA, ⟨a, hright⟩, hcont, fun R hR =>
    hR.unique F.canonicalTopologicalData.residueCardinality_gt_one hcont⟩

set_option maxHeartbeats 1600000 in
/-- A realized separated coefficient model has a uniform finite family whose
actual matrix rational values give the corank-one continuation by finite products.
The family precedes the second vector and its matrix coefficients precede all
spectral parameters and matrix rational-value witnesses. -/
theorem adjacentRankModel_corankOne_productContinuation
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F.Carrier) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (hU : ∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    ∃ (Lq Lh : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      (∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
        Lq ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) ∧
      (∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
        Lh ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier)) ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          let Winv := InducedTailIntermediate.scaledStandardAsInverse ψ W'.val
          let Binv := fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val
          ∀ M : Fin N → RationalFunctions,
            (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
              (generalLinearHaar F.Carrier r) Φ
              (fun h => (χ (GeneralLinear.determinant h) : ℂ) * (f i).val h) (M i)) →
            ∃ A : Fin N → RationalFunctions,
              (∀ i, HasRationalContinuation qF
                (fun s => equalRankIntegral ψ abv ν W.val (Binv i) φ s) (A i)) ∧
              (∃ a : ℝ, ∀ s : ℂ, a < s.re →
                CorankOneConverges ψ abv ν U.val Winv s ∧
                (∀ i, EqualRankConverges ψ abv ν W.val (Binv i) φ s) ∧
                (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
                  (fun h => (χ (GeneralLinear.determinant h) : ℂ) * (f i).val h)) ∧
                corankOneIntegral ψ abv ν U.val Winv s =
                  adjacentRankFiniteProductValue F ψ ν W.val Binv Φ φ χ
                    (fun i => (f i).val) s) ∧
              HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val Winv s)
                (∑ i, A i * M i) ∧
              ∀ R, HasRationalContinuation qF
                (fun s => corankOneIntegral ψ abv ν U.val Winv s) R →
                R = ∑ i, A i * M i := by
  obtain ⟨Lq, Lh, N, B, hLq, hLh, hB⟩ :=
    adjacentRankModel_corankOne_finiteConvolution F ψ μ hself σ hσ.1.1 ℓ χ Φ φ W
      U.val hU τ hτ.1 ℓ' ν hν
  refine ⟨Lq, Lh, N, B, hLq, hLh, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, ?_⟩
  dsimp only at hf ⊢
  intro M hM
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  exact corankOneCoefficient_productContinuation F ψ ν hν μ σ τ π hσ hτinv hπ ℓ
    (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ') ℓU hℓ hℓ' hℓU W
    (fun i => scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i)) U
    (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')
    Φ φ χ (fun i => (f i).val) Lq Lh hLq hLh hf.2.2.2 M hM

end Langlands.RankinSelberg.Padic
