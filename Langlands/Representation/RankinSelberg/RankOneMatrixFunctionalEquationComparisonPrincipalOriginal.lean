import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalRealization
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonOriginalExtraction

/-! # Actual original comparison for the uniform principal realization -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg
open scoped NNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalOriginalFourierTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalOriginalFourierValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalOriginalFourierLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalOriginalFourierScalarMeasurable : MeasurableSpace F.Carrier := borel _
local instance principalOriginalFourierScalarBorel : BorelSpace F.Carrier := ⟨rfl⟩

/-- Any supplied compact open full-test stabilizer fixes every Fourier partner
on its inverse-transpose side. -/
theorem compactOpen_matrixTest_fourier_invariant {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (Φ ΦHat : MatrixTestFunction n F.Carrier) (hpair : MatrixFourierPair F ψ ν Φ ΦHat)
    (hΦ : ∀ k ∈ K, ∀ M, Φ (k.val * M) = Φ M) :
    ∀ k ∈ inverseTransposeOpenSubgroup F K,
      (∀ M, ΦHat (k.val * M) = ΦHat M) ∧
        normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1 := by
  have hd := GodementJacquet.padicMatrixFourierPair_compact_left_invariant F
    F.canonicalTopologicalData n ψ ν K.toSubgroup hK Φ ΦHat hpair hΦ
  intro k hk
  constructor
  · apply hd k
    rw [← inverseTransposeOpenSubgroup_toSubgroup F K]
    exact hk
  · have hn := F.canonicalTopologicalData.determinantNorm_eq_one_of_mem_compact
      (n + 1) (inverseTransposeOpenSubgroup F K).toSubgroup
      (isCompact_inverseTransposeOpenSubgroup F K hK) k hk
    exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hn

end Langlands.GodementJacquet.Padic

namespace Langlands.RankinSelberg.RankOneBox

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Whittaker Conductor RankOneIwasawa
open scoped NNReal ENNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalOriginalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalOriginalValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalOriginalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalOriginalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalOriginalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalOriginalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The fixed uniform box has exactly its stated positive extraction constant
against the original rank-one integral, at each convergent matrix exponent. -/
theorem principalOriginal_value (hσ : IsSmooth σ) {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (hfixed : ∀ y ∈ principalLevelSubgroup F.Carrier (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (s : ℂ)
    (hconv : Integrable (GodementJacquet.matrixIntegrand abv
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a)
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
      (generalLinearHaar F.Carrier (m + 1))) :
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1))
      (boxLatticeTest F (F.canonicalTopologicalData.additiveConductor ψ + a)
        (F.canonicalTopologicalData.additiveConductor ψ) a)
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) =
    (boxExtractionConstant F (n := m + 1)
      (F.canonicalTopologicalData.additiveConductor ψ + a)
      (F.canonicalTopologicalData.additiveConductor ψ) a : ℂ) *
      ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g ∂generalLinearHaar F.Carrier 0 := by
  let C := boxExtractionConstant F (n := m + 1)
    (F.canonicalTopologicalData.additiveConductor ψ + a)
    (F.canonicalTopologicalData.additiveConductor ψ) a
  have hC : 0 ≤ C := (boxExtractionConstant_pos F hA ha).le
  obtain ⟨-, hv⟩ := principalMeasure_weighted_extraction F ψ ha hA
    (glModelFunction ψ (m + 1) σ ℓ w) (continuous_glModelFunction F ψ σ hσ ℓ w)
    (glModelFunction_equivariance ψ (m + 1) σ ℓ w)
    (s + GodementJacquet.jpssShift (m + 1)) hconv
  dsimp only [C] at hC
  simp only [principalWeightedScalarAverage, principalAveragingMeasure_fixed F a hC _ hfixed,
    mul_assoc, integral_const_mul] at hv
  rw [hv]
  congr 1
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F.Carrier =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
    weight_smul_integrand F ψ σ ℓ w s g)

/-- The actual uniform realization has a common half-plane of genuine original
matrix convergence and the original rank-one value with its prescribed scalar. -/
def PrincipalOriginalAssertions (hσ : IsSmooth σ) (a : ℕ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))) : Prop :=
  let c := F.canonicalTopologicalData.additiveConductor ψ
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  let f := GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  let C := boxExtractionConstant F (n := m + 1) (c + a) c a
  ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    Integrable (GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
      (generalLinearHaar F.Carrier (m + 1)) ∧
    GodementJacquet.matrixIntegral abv (generalLinearHaar F.Carrier (m + 1)) Φ
      (s + GodementJacquet.jpssShift (m + 1)) f.val =
      (C : ℂ) * ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g
        ∂generalLinearHaar F.Carrier 0

/-- No raw convergence assumption is added: matrix convergence of the actual
bi-smooth realization gives raw convergence by pointwise equality on the box. -/
theorem principalOriginalAssertions_of_realization (hσ : IsSmooth σ) {a : ℕ}
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)))
    (hp : PrincipalModelRealization F ψ σ ℓ w hσ a K hK)
    (hMatrix : GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    PrincipalOriginalAssertions F ψ σ ℓ w hσ a K hK := by
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨b, fun s hs => ?_⟩
  let c := F.canonicalTopologicalData.additiveConductor ψ
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  let f := GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  have he : GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) f.val =
    GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) := by
    dsimp only [Φ]
    rw [boxLatticeTest_eq_compactOpenIndicator]
    exact box_matrixIntegrand_eq_of_eq_on_box F hp.2.2.2.2.2.1 _
  have hc := hb Φ f s hs
  change Integrable _ _ at hc
  rw [he] at hc
  refine ⟨hc, ?_⟩
  change (∫ g, GodementJacquet.matrixIntegrand _ _ _ f.val g ∂_) = _
  rw [he]
  exact principalOriginal_value F ψ σ ℓ w hσ hp.1 hp.2.1 hp.2.2.1 s hc

end Langlands.RankinSelberg.RankOneBox
