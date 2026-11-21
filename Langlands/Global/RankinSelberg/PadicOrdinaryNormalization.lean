import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Representation.RankinSelberg.NormalizedZetaCombination
import Langlands.Representation.RankinSelberg.PadicOrdinaryNormalizedTests
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof

/-! # Normalization for each specified ordinary p-adic test -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uV uW

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.RankinSelberg
open HarmonicAnalysis MeasureTheory Polynomial QuotientIntegration Whittaker

/-- The entire normalization obtained from the Laurent numerator of a rational zeta value. -/
def ordinaryNormalizationOfRationalContinuation {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) {q : ℕ} (hq : 1 < q)
    (R : zetaSpan values) {I : ℂ → ℂ} (hI : HasRationalContinuation q I R) :
    OrdinaryIntegralNormalization I (fun s => (P.eval (spectralPoint q s))⁻¹) where
  value s := laurentEval (spectralUnit (Nat.zero_lt_one.trans hq) s) (hP.normalizedLaurent R)
  analytic s _ := analyticAt_laurentEval_spectralUnit hq _ s
  eq_on_right := hP.exists_eq_spectralNormalization_mul_L hq R hI

/-- The normalized Laurent value is bounded on every vertical strip. -/
theorem ordinaryNormalizationOfRationalContinuation_strip_bound
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P) {q : ℕ} (hq : 1 < q)
    (R : zetaSpan values) {I : ℂ → ℂ} (hI : HasRationalContinuation q I R) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(ordinaryNormalizationOfRationalContinuation hP hq R hI).value s‖ ≤ C :=
  exists_bound_laurentEval_spectralUnit hq (hP.normalizedLaurent R) a b

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance padicOrdinaryTopology : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance padicOrdinaryValuation : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance padicOrdinaryLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance padicOrdinaryFieldMeasurable : MeasurableSpace K.Carrier := borel K.Carrier
local instance padicOrdinaryFieldBorel : BorelSpace K.Carrier := ⟨rfl⟩
local instance padicOrdinaryGroupMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) K.Carrier) := borel _
local instance padicOrdinaryGroupBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
local instance padicOrdinaryUnipotentMeasurable (n : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (n + 1) K.Carrier) := borel _
local instance padicOrdinaryUnipotentBorel (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
local instance padicOrdinaryQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n K.Carrier) := borel _
local instance padicOrdinaryQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩

local notation "qK" => K.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue K.canonicalTopologicalData
local notation "μ" n => unipotentQuotientHaar K.Carrier n

variable (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
  {n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {P : ℂ[X]}

/-- Every specified ordinary equal-rank coefficient-model integral has a strip-bounded entire
normalization for the canonical quotient measure. -/
theorem exists_padicOrdinaryEqualNormalization
    {π : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V}
    {σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W}
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hP : IsPadicPairLPolynomial K ψ ν π σ P)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → K.Carrier)) :
    ∃ N : OrdinaryIntegralNormalization (equalRankModelIntegral ψ abv (μ n) π σ ℓ ℓ' f f' Φ)
      (fun s => (P.eval (spectralPoint qK s))⁻¹),
      ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖N.value s‖ ≤ C := by
  have hAnalytic := equalRankAnalytic.{u, uV, uW} K K.canonicalTopologicalData n ψ (μ n)
    (unipotentQuotientHaar_isCompatible K.Carrier n) V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨R, hR⟩ := hAnalytic.2.1 f f' Φ
  have hMem := equalRankModel_mem_zetaValues qK ψ abv (μ n) ℓ ℓ' f f' Φ
    (hAnalytic.1 f f' Φ) hR
  let r : zetaSpan (padicOrdinaryEqualZetaValues K ψ π σ) := ⟨R, mem_zetaSpan hMem⟩
  let hGen := hP.normalizedGenerator_ordinaryEqual
  let hq := K.canonicalTopologicalData.residueCardinality_gt_one
  exact ⟨ordinaryNormalizationOfRationalContinuation hGen hq r hR,
    ordinaryNormalizationOfRationalContinuation_strip_bound hGen hq r hR⟩

/-- Every specified ordinary block-zero unequal-rank coefficient-model integral has a
strip-bounded entire normalization for the canonical quotient measure. -/
theorem exists_padicOrdinaryUnequalNormalization {k : ℕ}
    {π : Representation ℂ (GeneralLinear (n + (0 + k + 1) + 1) K.Carrier) V}
    {σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) W}
    (hπ : IsOfWhittakerType (n + (0 + k + 1)) (standardCharacter ψ (n + (0 + k + 1))) π)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hP : IsPadicPairLPolynomial K ψ ν π σ P)
    (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ N : OrdinaryIntegralNormalization
      (unequalRankModelIntegral ψ abv 0 k (μ n) (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ' f f')
      (fun s => (P.eval (spectralPoint qK s))⁻¹),
      ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖N.value s‖ ≤ C := by
  have hAnalytic := unequalRankAnalytic.{u, uV, uW} K K.canonicalTopologicalData n 0 k ψ (μ n)
    (unipotentQuotientHaar_isCompatible K.Carrier n) ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨R, hR⟩ := hAnalytic.2.1 f f'
  have hMem := unequalRankModel_mem_zetaValues qK ψ abv 0 k (μ n)
    (rectangularMeasure ν 0 (n + 1)) ℓ ℓ' f f' (hAnalytic.1 f f') hR
  let r : zetaSpan (padicOrdinaryUnequalZetaValues K ψ ν k π σ) := ⟨R, mem_zetaSpan hMem⟩
  let hGen := hP.normalizedGenerator_ordinaryUnequal
  let hq := K.canonicalTopologicalData.residueCardinality_gt_one
  exact ⟨ordinaryNormalizationOfRationalContinuation hGen hq r hR,
    ordinaryNormalizationOfRationalContinuation_strip_bound hGen hq r hR⟩

end Langlands.Global.RankinSelbergGlobal
