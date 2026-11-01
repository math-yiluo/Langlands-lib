import Langlands.Representation.RankinSelberg.BilateralSpectralEvaluation
import Langlands.Representation.RankinSelberg.AdjacentRankSpectralExpansion
import Langlands.Representation.RankinSelberg.AdjacentRankProductDenominatorBound
import Langlands.Representation.RankinSelberg.LaurentTransport

/-! From actual cleared bilateral coefficients to rational denominator bounds. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open BilateralSpectralEvaluation
open scoped BigOperators

/-- A scalar function is the actual convergent spectral sum of a bilateral
coefficient series on a right half-plane. -/
def HasBilateralSpectralExpansion
    (q : ℕ) (a : BilateralLaurentSeries) (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ s : ℂ, C < s.re →
    HasSum (fun m : ℤ => a m * spectralPoint q s ^ m) (f s)

/-- Formal clearing and convergent spectral sums identify the cleared rational
continuation. No polynomial is canceled in the bilateral series module. -/
theorem clearedSpectralExpansion_rationalIdentity
    {q : ℕ} (hq : 1 < q) (a : BilateralLaurentSeries) (f : ℂ → ℂ)
    (P : Polynomial ℂ) (Q : LaurentPolynomial ℂ) (R : RationalFunctions)
    (hexp : HasBilateralSpectralExpansion q a f)
    (hclear : BilateralLaurentSeries.ofLaurentPolynomial Q = P.toLaurent • a)
    (hR : HasRationalContinuation q f R) :
    laurentToRatFunc Q = algebraMap (Polynomial ℂ) RationalFunctions P * R := by
  have hqpos : 0 < q := lt_trans Nat.zero_lt_one hq
  obtain ⟨C, hC⟩ := hexp
  have hQ : HasRationalContinuation q
      (fun s => P.eval (spectralPoint q s) * f s) (laurentToRatFunc Q) := by
    refine ⟨C, fun s hs => ?_⟩
    let x := spectralUnit hqpos s
    have hsum := hasSum_laurent_smul x P.toLaurent a (f s) (hC s hs)
    have hfinite := hasSum_ofLaurentPolynomial x Q
    rw [hclear] at hfinite
    have hvalue : laurentEval x Q = P.eval (spectralPoint q s) * f s := by
      simpa only [laurentEval_toLaurent, x, coe_spectralUnit] using hfinite.unique hsum
    exact ⟨laurentToRatFunc_regular x Q,
      hvalue.symm.trans (eval_laurentToRatFunc x Q).symm⟩
  have hP : HasRationalContinuation q (fun s => P.eval (spectralPoint q s))
      (algebraMap (Polynomial ℂ) RationalFunctions P) := by
    refine ⟨0, fun s _ => ?_⟩
    simp
  exact hQ.unique hq (hP.mul hR)

/-- A nonzero clearing polynomial bounds the rational continuation by its
reciprocal Laurent span, after scalar convergence has supplied the identity. -/
theorem clearedSpectralExpansion_mem_reciprocalSpan
    {q : ℕ} (hq : 1 < q) (a : BilateralLaurentSeries) (f : ℂ → ℂ)
    (P : Polynomial ℂ) (hP : P ≠ 0) (R : RationalFunctions)
    (hexp : HasBilateralSpectralExpansion q a f)
    (hclear : ∃ Q : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial Q = P.toLaurent • a)
    (hR : HasRationalContinuation q f R) :
    R ∈ Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} := by
  obtain ⟨Q, hQ⟩ := hclear
  have hidentity := clearedSpectralExpansion_rationalIdentity hq a f P Q R hexp hQ hR
  refine Submodule.mem_span_singleton.mpr ⟨Q, ?_⟩
  rw [Algebra.smul_def, algebraMap_laurent, hidentity, mul_right_comm,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hP), one_mul]

namespace Padic

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance clearedContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance clearedContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance clearedContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance clearedContinuationFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance clearedContinuationFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance clearedContinuationGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance clearedContinuationGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance clearedContinuationUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance clearedContinuationUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance clearedContinuationQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance clearedContinuationQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T

/-- Clearing the actual corank slice coefficients bounds every rational
continuation, provided the original integrals converge on a right half-plane. -/
theorem corankClearing_denominatorBound
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (U : WhittakerFunctions ψ (r + 1)) (Wprime : InverseWhittakerFunctions ψ r)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hconv : ∃ C : ℝ, ∀ s : ℂ, C < s.re →
      Integrable (corankOneIntegrand ψ abv U Wprime s) ν)
    (hclear : let a : BilateralLaurentSeries := fun m =>
        sliceCoefficient T ν (corankOneIntegrand ψ abv U Wprime 0) m
      ∃ Q : LaurentPolynomial ℂ,
        BilateralLaurentSeries.ofLaurentPolynomial Q = P.toLaurent • a) :
    AdjacentRankCorankDenominatorBound F ψ ν U Wprime P := by
  let a : BilateralLaurentSeries := fun m =>
    sliceCoefficient T ν (corankOneIntegrand ψ abv U Wprime 0) m
  have hexp : HasBilateralSpectralExpansion F.canonicalTopologicalData.residueCardinality a
      (fun s => corankOneIntegral ψ abv ν U Wprime s) := by
    obtain ⟨C, hC⟩ := hconv
    exact ⟨C, fun s hs => (corankOneSliceExpansion F ψ U Wprime ν s (hC s hs)).2⟩
  intro R hR
  exact clearedSpectralExpansion_mem_reciprocalSpan
    F.canonicalTopologicalData.residueCardinality_gt_one a
      (fun s => corankOneIntegral ψ abv ν U Wprime s) P hP R hexp hclear hR

/-- The published full-type corank convergence theorem discharges the
convergence input for actual nonzero functional images. -/
theorem corankOneCoefficient_clearing_denominatorBound
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear ((r + 1) + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (U : (coefficientModel π ℓU).toSubmodule)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hclear : let a : BilateralLaurentSeries := fun m =>
        sliceCoefficient T ν (corankOneIntegrand ψ abv U.val Wprime.val 0) m
      ∃ Q : LaurentPolynomial ℂ,
        BilateralLaurentSeries.ofLaurentPolynomial Q = P.toLaurent • a) :
    AdjacentRankCorankDenominatorBound F ψ ν U.val Wprime.val P := by
  apply corankClearing_denominatorBound F ψ ν U.val Wprime.val P hP
    (corankOneCoefficient_convergesOnRight F ψ ν hν μ π τ hπ hτ
      ℓU ℓprime hℓU hℓprime U Wprime) hclear

end Padic
end Langlands.RankinSelberg
