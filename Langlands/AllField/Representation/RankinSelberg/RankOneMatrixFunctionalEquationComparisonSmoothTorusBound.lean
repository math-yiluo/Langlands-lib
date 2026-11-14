import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSmoothTorusBound
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.PadicBlocksSupplement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof
/-! Discrete torus bounds for the actual smooth matrix coefficient family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement matrixIntegrand_exists_principalFixed measurable_biSmooth_matrixIntegrand normalizedAbsoluteValue normalizedAbsoluteValue_apply smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear
open Langlands.Conductor
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped ENNReal NNReal

universe uF uV uG

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance smoothTorusGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance smoothTorusGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The entire matrix integrand has a principal right stabilizer independent
of the spectral exponent. -/
theorem matrixIntegrand_exists_principalFixed
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients σ) :
    ∃ a : ℕ, 0 < a ∧ ∀ s : ℂ,
      ∀ k ∈ principalLevelSubgroup F n a, ∀ g,
        matrixIntegrand abv Φ s f.val (g * k) = matrixIntegrand abv Φ s f.val g := by
  obtain ⟨hc, K, hK⟩ := biSmoothMatrixCoefficient_continuous_rightFixed σ f
  have ht : Filter.Tendsto
      (fun k : Langlands.GeneralLinear (n + 1) F =>
        ((1 : Langlands.GeneralLinear (n + 1) F), k))
      (𝓝 1) (𝓝 (1, 1)) :=
    (continuous_const.prodMk continuous_id).tendsto _
  have hΦ : {k : Langlands.GeneralLinear (n + 1) F |
      ∀ X, Φ (X * k.val) = Φ X} ∈ 𝓝 1 := by
    change ∀ᶠ k in 𝓝 (1 : Langlands.GeneralLinear (n + 1) F),
      ∀ X, Φ (X * k.val) = Φ X
    simpa only [Units.val_one, Matrix.one_mul] using
      ht.eventually (eventually_matrixTranslate_eq Φ)
  obtain ⟨a, ha, haU⟩ := exists_pos_principalLevelOpenSubgroup_subset F n
    (Filter.inter_mem (K.isOpen.mem_nhds K.one_mem) hΦ)
  refine ⟨a, ha, ?_⟩
  intro s k hk g
  have hkg := haU hk
  have hnorm := (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_mem_compact
    (n + 1) (principalLevelSubgroup F n a)
    (isCompact_principalLevelOpenSubgroup F n a) k hk
  have hdet : abv (Matrix.det k.val) = 1 := by
    simpa using congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hnorm
  simp only [matrixIntegrand, Units.val_mul, hkg.2 g.val, hK k hkg.1 g, determinantWeight,
    Matrix.det_mul, map_mul, hdet, mul_one]

/-- Measurability of the genuine integrand, including its complex spectral
weight, for every member of the actual bi-smooth coefficient span. -/
theorem measurable_biSmooth_matrixIntegrand
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients σ) (s : ℂ) :
    Measurable (matrixIntegrand abv Φ s f.val) := by
  have hf := (biSmoothMatrixCoefficient_continuous_rightFixed σ f).1
  have hc : Continuous fun g : Langlands.GeneralLinear (n + 1) F =>
      ((abv (Matrix.det g.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp
      ((⟨⟩ : LocalFieldData F).determinantNormContinuous (n + 1)).continuous))
  exact ((Φ.continuous.comp Units.continuous_val).measurable.mul hf.measurable).mul
    (hc.measurable.pow_const s)

end Langlands.AllField.RankinSelberg
