import Langlands.TraceFormula.SingleOrbitSimpleTrace
import Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof
import Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingProof
import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction

/-!
# The simple trace formula for one tensor test isolating one rational class

See `GeneralLinearTensorSingleOrbitTrace.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported ENNReal

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands Langlands.BaseChange
open Langlands.Analysis.OperatorIdeals

universe u

local instance tensorSingleOrbitIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance tensorSingleOrbitSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

set_option maxRecDepth 3500 in
set_option maxHeartbeats 4200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Single-orbit trace for one tensor test.** Assume that the cuspidal operators of tensor
tests are Hilbert–Schmidt. Let `f = a ⊗ b` be a tensor test whose finite factor integrates to
zero along every two-sided translate of every two-block unipotent radical at a finite place `w`,
and whose support is regular elliptic at a finite place `v`. If every rational norm-one element
with a conjugate on which the positive average `f¹` does not vanish is rationally conjugate to
`r₀`, then `R(f)` is trace class and its trace is the volume times the orbital integral of `f¹`
at `r₀`, for every choice of compatible measures at `r₀`. -/
theorem generalLinearTensorSingleOrbitTrace
    (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    (hHS : ∀ (a : ArchimedeanGL.SmoothCompactKernel K n) (b : CompactFiniteGLTest K n)
      (h : Integrable (fun g => adelicTestTensor K n a b
        (GeneralLinearGroupPoints.adelicHomeomorph K n g))
        (Measure.haar : Measure (AdelicGroupPoints K GLₙ))),
      IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc Measure.haar
        (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g)) h))
    (a : ArchimedeanGL.SmoothCompactKernel K n) (b : CompactFiniteGLTest K n)
    (w : Langlands.Global.FinitePlace K)
    (hloc : ∀ (p q : ℕ) (hpq : p + q = n), 0 < p → 0 < q →
      letI : MeasurableSpace (Matrix (Fin p) (Fin q) (FiniteCompletion K w)) := borel _
      ∀ ν : Measure (Matrix (Fin p) (Fin q) (FiniteCompletion K w)), ν.IsAddHaarMeasure →
        ∀ x y : FiniteAdelicGL K n,
          ∫ Z, b.val (x * FiniteAdelicGL.localInclusion K n w (GeneralLinear.blockUnipotent hpq Z) * y) ∂ν = 0)
    (v : Langlands.Global.FinitePlace K)
    (hell : ∀ g ∈ tsupport (adelicTestTensor K n a b),
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v (AdelicGL.finite K n g)))
    (r₀ : rationalNormOneSubgroup K GLₙ)
    (d₀ : TwistedGeometricMeasures (rationalNormOneSubgroup K GLₙ)
      (MonoidHom.id (normOneSubgroup K GLₙ)) (r₀ : normOneSubgroup K GLₙ) Measure.haar)
    (hIso : ∀ q : rationalNormOneSubgroup K GLₙ,
      (∃ x : normOneSubgroup K GLₙ, normOnePositiveAverage K GLₙ T i
          (normalizedPositiveHaarMeasure K GLₙ T i hi I e hc)
          (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g))
          (x⁻¹ * (q : normOneSubgroup K GLₙ) * x) ≠ 0) →
        IsTwistedConjugate (rationalNormOneSubgroup K GLₙ) (MonoidHom.id (normOneSubgroup K GLₙ))
          (q : normOneSubgroup K GLₙ) (r₀ : normOneSubgroup K GLₙ)) :
    ∃ h : Integrable (fun g => adelicTestTensor K n a b
        (GeneralLinearGroupPoints.adelicHomeomorph K n g)) (Measure.haar : Measure (AdelicGroupPoints K GLₙ)),
      let X := haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h
      IsTraceClass X ∧
        (d₀.orbitalValue (normOnePositiveAverage K GLₙ T i
          (normalizedPositiveHaarMeasure K GLₙ T i hi I e hc)
          (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g))) ≠ 0 →
          d₀.rational Set.univ ≠ ⊤) ∧
        operatorTrace X = d₀.term (normOnePositiveAverage K GLₙ T i
          (normalizedPositiveHaarMeasure K GLₙ T i hi I e hc)
          (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g))) := by
  have hTF := generalLinearTensorSimpleTraceFormula_of_simpleTraceFormula
    generalLinearSimpleTraceFormula generalLinearRadicalIntegralVanishing
  have key := hTF K n hPD hG T i hi I e hc hHS 1 (fun _ => a)
    (fun _ => b) (fun _ => w) (fun _ p q hpq hp hq => hloc p q hpq hp hq) v (fun _ => hell)
  have hfun : (fun g : AdelicGroupPoints K GLₙ =>
      ∑ j : Fin 1, adelicTestTensor K n ((fun _ => a) j) ((fun _ => b) j)
        (GeneralLinearGroupPoints.adelicHomeomorph K n g)) =
      fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g) := by
    funext g
    simp only [Fin.sum_univ_one]
  revert key
  rw [hfun]
  rintro ⟨h, hClass, m, r, hDistinct, hReg, hCover, hSum⟩
  let H := normOneSubgroup K GLₙ
  let R := rationalNormOneSubgroup K GLₙ
  let θ := MonoidHom.id H
  let μH : Measure H := Measure.haar
  let fOne := normOnePositiveAverage K GLₙ T i (normalizedPositiveHaarMeasure K GLₙ T i hi I e hc)
    (fun g => adelicTestTensor K n a b (GeneralLinearGroupPoints.adelicHomeomorph K n g))
  let X := haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h
  have hAvail (j : Fin m) : Nonempty (TwistedGeometricMeasures R θ (r j : H) μH) :=
    nonempty_twistedGeometricMeasures_of_commutative (isDiscrete_rationalNormOneSubgroup K GLₙ)
      continuous_id (generalLinearRegularCentralizerCommutative K n v (r j) (hReg j))
  have hBlock : SimpleTraceGeometricExpansion R θ μH fOne (operatorTrace X) r := hSum
  exact ⟨h, hClass, singleOrbitGeometricTrace r₀ d₀ fOne (operatorTrace X) r
    hDistinct (fun q hq => hCover q q.property hq) hIso hAvail
    (bundledGeometricTraceSum R θ μH fOne (operatorTrace X) r hBlock)⟩

end Langlands.TraceFormula
